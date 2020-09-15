#!/usr/bin/env python

from manimlib.imports import *

import itertools as it
import uuid

LAVENDER_ISH = '#ADA6FF'

# From: https://stackoverflow.com/a/1482316/1498618
def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return list(it.chain.from_iterable(it.combinations(s, r) for r in range(len(s)+1)))

# From: https://stackoverflow.com/a/5656097/1498618
def intersperse(delim, iterable):
    it = iter(iterable)
    yield next(it)
    for x in it:
        yield delim
        yield x

def radius_of(obj):
    return 0.5 * 0.5 * (obj.get_width() + obj.get_height())

PLAYER_ONE_COLOR = RED
PLAYER_TWO_COLOR = BLUE

class GameTreePosition(VGroup):
    def __init__(self, shape, parent):
        super().__init__(shape)
        self.shape = shape
        self.parent = parent
        self.parent_edge = None
        self.children = []
        self.player1_wins = None

    def add_child(self, child):
        self.children.append(child)

    def creation_anims(self):
        if self.parent is None:
            self.parent_edge = None
            return [ ShowCreation(self.shape) ]
        else:
            self.parent_edge = Line(self.parent.shape, self.shape)
            super().__init__(self.shape, self.parent_edge)
            return [ ShowCreation(self.shape), ShowCreation(self.parent_edge) ]

    def update_group(self):
        if self.parent_edge is not None:
            super().__init__(self.shape, self.parent_edge)
        else:
            super().__init__(self.shape)

    def winner_anims(self):
        if self.player1_wins is not None:
            if self.player1_wins:
                return [ ApplyMethod(self.shape.set_color, PLAYER_ONE_COLOR) ]
            else:
                return [ ApplyMethod(self.shape.set_color, PLAYER_TWO_COLOR) ]
        else:
            return [ ApplyMethod(self.shape.set_color, WHITE) ]

    def with_player1_wins(self, winner):
        self.player1_wins = winner
        return self

    def solve(self, p1Move):
        if self.player1_wins is not None:
            return self.player1_wins

        winners = []
        for pos in self.children:
            winners.append(pos.solve(not p1Move))

        if p1Move:
            # If it's player 1's turn, then they win if any of the next moves are winning positions for player 1
            self.player1_wins = any(winners)
        else:
            # If it's player 2's turn, then they win if any of the next moves are **not** winning positions for player 1
            # However, this means that player1 wins if **all** of the next moves are winning for player 1
            self.player1_wins = all(winners)

        return self.player1_wins

    def fade_anims(self):
        anims = []
        if self.parent_edge is not None:
            anims.append(FadeOut(self.parent_edge))
        anims.append(FadeOut(self.shape))
        return anims + [ anim for child in self.children for anim in child.fade_anims() ]

    def label_positions(self, current_label, scene, slow_anim=False):
        if current_label == "":
            pos_label = TextMobject("$\\varepsilon$")
        else:
            pos_label = TextMobject("$" + current_label + "$")
        pos_label.scale(2.0*radius_of(self.shape))
        pos_label.move_to(self.shape)

        anims = []

        if slow_anim:
            scene.play(Write(pos_label))
            scene.wait()
        else:
            anims.append(Write(pos_label))

        labels = [ pos_label ]
        for i, child in enumerate(self.children):
            if slow_anim:
                labels += child.label_positions(current_label + str(i + 1), scene, slow_anim=slow_anim)
            else:
                new_labels, new_anims = child.label_positions(current_label + str(i + 1), scene, slow_anim=slow_anim)
                labels += new_labels
                anims += new_anims

        if slow_anim:
            return labels
        else:
            return labels, anims

class GameTree(VGroup):
    def __init__(self, depth, child_nums=None, layer_widths=None, max_child_num=3):
        self.layers = []

        self.starting_position = GameTreePosition(Circle(color=WHITE), None)
        self.starting_position.scale(0.5)
        self.starting_position.shift(3*UP)

        self.layers.append([ self.starting_position ])

        self.positions = [ self.starting_position ]

        if layer_widths is None:
            layer_widths = [ 5.0 ]

        for i in range(depth):
            new_layer = []
            for pos in self.layers[-1]:
                layer_width = layer_widths.pop(0)

                if child_nums is not None and len(child_nums) > 0:
                    child_num = child_nums.pop(0)
                else:
                    child_num = random.randint(1, max_child_num)

                new_layer += self.draw_position_layer(pos, child_num, layer_width=layer_width)
                for j in range(child_num):
                    layer_widths.append(0.9 * layer_width / child_num)

            self.positions += new_layer
            self.layers.append(new_layer)

        super().__init__(*self.positions)

    def draw_position_layer(self, parent, num, layer_width=6, shape_gen=lambda size: Circle(color=WHITE).scale(size)):
        if num == 1:
            radius = radius_of(parent) * 0.8
        else:
            radius = min(radius_of(parent) * 0.8, 0.5 * layer_width / (1.5 * (num - 1)))

        new_positions = []
        for i in range(num):
            pos = GameTreePosition(shape_gen(radius), parent)
            parent.add_child(pos)
            pos.move_to(parent)
            pos.shift(DOWN)
            if num > 1:
                pos.shift(0.5*layer_width*LEFT)
                pos.shift(layer_width/(num - 1)*i*RIGHT)

            new_positions.append(pos)

        return new_positions

    def show_creation(self, scene, slow_anim=False):
        if slow_anim:
            for layer in self.layers:
                scene.play(*[ anim for pos in layer for anim in pos.creation_anims() ])
                scene.wait()
        else:
            scene.play(*[ anim for layer in self.layers for pos in layer for anim in pos.creation_anims() ])
            scene.wait()

    def show_solving(self, scene, slow_anim=False):
        # Show from bottom to top because that is more intuitive probably
        for layer in self.layers[::-1]:
            if slow_anim:
                for pos in layer:
                    scene.play(*pos.winner_anims())
                    scene.wait()
            else:
                scene.play(*[anim for pos in layer for anim in pos.winner_anims() ])
                scene.wait()

    def show_player_turns(self, scene, slow_anim=False):
        is_player_1_turn = True
        turn_labels = []
        anims = []

        # The last position doesn't really count as a "move"
        for i, layer in enumerate(self.layers[:-1]):
            if is_player_1_turn:
                turn_label = TextMobject("Player 1")
                turn_label.set_color(PLAYER_ONE_COLOR)
            else:
                turn_label = TextMobject("Player 2")
                turn_label.set_color(PLAYER_TWO_COLOR)
            turn_label.scale(0.5)
            turn_label.move_to(self.starting_position)
            turn_label.shift(i*DOWN)
            turn_label.shift(5*LEFT)

            if slow_anim:
                scene.play(Write(turn_label))
                scene.wait()
            else:
                anims.append(Write(turn_label))

            is_player_1_turn = not is_player_1_turn

            turn_labels.append(turn_label)

        if not slow_anim:
            scene.play(*anims)
            scene.wait()

        return turn_labels

    def label_positions(self, scene, slow_anim=False):
        if slow_anim:
            return self.starting_position.label_positions("", scene, slow_anim=slow_anim)
        else:
            labels, anims = self.starting_position.label_positions("", scene, slow_anim=slow_anim)
            scene.play(*anims)
            scene.wait()
            return labels

    def solve(self):
        self.starting_position.solve(True)

    def recenter(self, layer_num, zoom_pos, scene, slow_anim=False):
        old_start = self.starting_position
        old_positions = [ pos for layer in self.layers[1:layer_num] for pos in layer ] + [ pos for pos in self.layers[layer_num] if pos != zoom_pos ]
        self.layers = [ [ zoom_pos ] ]
        to_add = [ zoom_pos ]

        while len(to_add) > 0:
            new_layer = [ child for pos in to_add for child in pos.children ]
            to_add = new_layer
            if len(new_layer) > 0:
                self.layers.append(new_layer)

        anims = [ FadeOut(self.starting_position.shape) ]
        anims += [ anim for pos in old_positions for anim in pos.fade_anims() ]
        if zoom_pos.parent_edge is not None:
            anims.append(FadeOut(zoom_pos.parent_edge))
            zoom_pos.parent_edge = None
            zoom_pos.update_group()

        scene.play(*anims)

        if slow_anim:
            scene.wait()

        self.starting_position = zoom_pos

        self.positions = [ pos for layer in self.layers for pos in layer ]
        super().__init__(*self.positions)

        scene.play(Transform(self.starting_position, old_start))
        # scene.play(ApplyMethod(self.starting_position.scale, radius_of(old_start.shape) / radius_of(self.starting_position.shape)))
        # scene.play(ApplyMethod(self.move_to, old_start.get_center()))

        if slow_anim:
            scene.wait()

    def add_layer(self, min_child_num=1, max_child_num=3, layer_width=8.0, child_nums=None):
        if child_nums is None:
            child_nums = []

        new_layer = []
        for pos in self.layers[-1]:
            if child_nums is not None and len(child_nums) > 0:
                child_num = child_nums.pop(0)
            else:
                child_num = random.randint(min_child_num, max_child_num)

            new_layer += self.draw_position_layer(pos, child_num, layer_width=layer_width)

        self.positions += new_layer
        self.layers.append(new_layer)

        super().__init__(*self.positions)

        return [ anim for pos in new_layer for anim in pos.creation_anims() ]

MY_GREEN = "#6be086"
PALE_PINK = "#ffe8e9"

class ChessPiece(VGroup):
    def __init__(self, color, name):
        self.color = color
        self.name = name
        self.shape = Circle(color=self.color, fill_color=self.color, fill_opacity=1)
        self.shape.scale(0.2)
        super().__init(self.shape)

class Chessboard(VGroup):
    def __init__(self):
        self.pieces = []

        self.board = []

        cur_color = PALE_PINK
        for x in range(8):
            new_row = []
            for y in range(8):
                new_shape = Square(color=cur_color, fill_color=cur_color, fill_opacity=1)
                new_shape.scale(0.3)
                new_shape.shift((x - 4) * 0.62 * RIGHT)
                new_shape.shift((y - 4) * 0.62 * DOWN)
                new_row.append(new_shape)

                cur_color = MY_GREEN if cur_color == PALE_PINK else PALE_PINK
            cur_color = MY_GREEN if cur_color == PALE_PINK else PALE_PINK
            self.board.append(new_row)

        super().__init__(*[ square for row in self.board for square in row ])

class GamesDetermined(Scene):
    def construct(self):
        self.introduction()
        self.define_game()
        self.show_outline(1)
        self.define_determined()
        self.show_outline(2)
        self.prove_finite_games_determined()
        self.show_outline(3)
        # TODO: Final part

    def introduction(self):
        title = TextMobject("Who wins in Chess?")
        self.play(Write(title))
        self.wait(3)

        subtitle = TextMobject("(why all finite games are determined)")
        subtitle.scale(0.5)
        subtitle.next_to(title, DOWN)
        self.play(Write(subtitle))
        self.wait(2)

        self.play(ApplyMethod(title.shift, 3*UP), ApplyMethod(subtitle.shift, 3*UP))
        self.wait()

        chessboard = Chessboard()
        chessboard.next_to(subtitle, DOWN)
        self.play(FadeIn(chessboard))
        self.wait(20)

        self.play(ApplyMethod(chessboard.scale, 0.7))
        self.play(ApplyMethod(chessboard.shift, 3*LEFT))
        self.wait(10)

        texts = self.build_outline(chessboard,
                [ "$\\square$ What is a (finite) game?",
                  "$\\square$ When is a game \\textit{determined}?",
                  "$\\square$ All finite games are determined (+ proof).",
                  "$\\square$ Infinite games and more."], 0, slow_anim=True)
        self.wait()

        self.play(FadeOut(chessboard), FadeOut(subtitle), FadeOut(title), *[ FadeOut(text) for text in texts ])
        self.wait()

    def show_outline(self, topic_idx, slow_anim=False):
        chessboard = Chessboard()
        chessboard.scale(0.7)
        chessboard.shift(3*LEFT)
        self.play(FadeIn(chessboard))

        texts = self.build_outline(chessboard,
                [ "$\\square$ What is a (finite) game?",
                  "$\\square$ When is a game \\textit{determined}?",
                  "$\\square$ All finite games are determined (+ proof).",
                  "$\\square$ Infinite games and more."], topic_idx, slow_anim=slow_anim)
        self.wait(10)

        self.play(FadeOut(chessboard), *[ FadeOut(text) for text in texts ])
        self.wait()

    def build_outline(self, chessboard, topics, cur_topic_idx, slow_anim=False):
        topic_texts = []
        anims = []

        for i, topic in enumerate(topics):
            topic_text = TextMobject(topic)
            topic_text.scale(0.8)
            topic_text.next_to(chessboard.get_corner(UP + RIGHT), RIGHT)
            topic_text.shift(0.2*DOWN)
            topic_text.shift(i*DOWN)

            if slow_anim:
                self.play(Write(topic_text))
                self.wait(2)
            else:
                anims.append(Write(topic_text))

            topic_texts.append(topic_text)

        if not slow_anim:
            self.play(*anims)
            self.wait()

        self.play(ApplyMethod(topic_texts[cur_topic_idx].set_color, MY_GREEN))

        return topic_texts

    def prove_finite_games_determined(self):
        theorem = self.introduce_theorem("(Zermelo) All finite games are determined.")

        contradict = TextMobject("\\textbf{\\underline{Proof.}} Suppose not.")
        contradict.scale(0.8)
        contradict.next_to(theorem, DOWN)
        contradict.shift(3*LEFT)
        self.play(Write(contradict))
        self.wait()

        game_tree = GameTree(1, child_nums=[7], layer_widths=[12])
        game_tree.shift(2*DOWN)
        game_tree.show_creation(self)

        # Discuss how neither player has a winning strategy.

        # Color the next layer
        for pos in game_tree.layers[1]:
            pos.with_player1_wins(random.random() < 0.5)
        self.play(*[ anim for pos in game_tree.layers[1] for anim in pos.winner_anims()])
        self.wait()

        turn_counter = TextMobject("Turn:~~~", "Player $1$")
        player_1_counter = TextMobject("Turn:~~~", "Player $1$")
        player_2_counter = TextMobject("Turn:~~~", "Player $2$")
        turn_counter.scale(0.8)
        turn_counter.next_to(contradict, DOWN)
        turn_counter.set_color(PLAYER_ONE_COLOR)
        player_1_counter.scale(0.8)
        player_1_counter.next_to(contradict, DOWN)
        player_1_counter.set_color(PLAYER_ONE_COLOR)
        player_2_counter.scale(0.8)
        player_2_counter.next_to(contradict, DOWN)
        player_2_counter.set_color(PLAYER_TWO_COLOR)
        self.play(Write(turn_counter))
        self.wait()

        # Every next position must be not be a win for player 1
        zoom_pos = None
        for pos in game_tree.layers[1]:
            if pos.player1_wins:
                pos.with_player1_wins(None)
                zoom_pos = pos
        self.play(*[anim for pos in game_tree.layers[1] for anim in pos.winner_anims() if pos.player1_wins is None])
        self.wait()
        game_tree.recenter(1, zoom_pos, self, slow_anim=True)
        self.wait()

        self.play(Transform(turn_counter, player_2_counter))
        self.wait()

        self.play(*game_tree.add_layer(child_nums=[4]))
        self.wait()

        for pos in game_tree.layers[1]:
            pos.with_player1_wins(random.random() < 0.5)
        self.play(*[ anim for pos in game_tree.layers[1] for anim in pos.winner_anims()])
        self.wait()

        for pos in game_tree.layers[1]:
            if not pos.player1_wins:
                pos.with_player1_wins(None)
                zoom_pos = pos
        self.play(*[anim for pos in game_tree.layers[1] for anim in pos.winner_anims() if pos.player1_wins is None])
        self.wait()

        is_player_1_turn = True
        # Repeat the above a bunch, basically, to make the point that it can be done infinitely
        for i in range(15):
            game_tree.recenter(1, zoom_pos, self)

            if is_player_1_turn:
                self.play(Transform(turn_counter, player_1_counter), run_time=0.2)
            else:
                self.play(Transform(turn_counter, player_2_counter), run_time=0.2)

            self.play(*game_tree.add_layer(min_child_num=2, max_child_num=10), run_time=0.2)

            for pos in game_tree.layers[1]:
                pos.with_player1_wins(random.random() < 0.5)

            # Make sure they're not all the same, or flip one
            if all([ pos.player1_wins for pos in game_tree.layers[1] ]) or all([ not(pos.player1_wins) for pos in game_tree.layers[1] ]):
                idx = random.randint(0, len(game_tree.layers[1]) - 1)
                game_tree.layers[1][idx].player1_wins = not game_tree.layers[1][idx].player1_wins

            self.play(*[ anim for pos in game_tree.layers[1] for anim in pos.winner_anims()])

            for pos in game_tree.layers[1]:
                if is_player_1_turn:
                    if pos.player1_wins:
                        pos.with_player1_wins(None)
                        zoom_pos = pos
                else:
                    if not pos.player1_wins:
                        pos.with_player1_wins(None)
                        zoom_pos = pos
            self.play(*[anim for pos in game_tree.layers[1] for anim in pos.winner_anims() if pos.player1_wins is None], run_time=0.2)

            is_player_1_turn = not is_player_1_turn

        contradict_finish = TextMobject("But then the game is \\textbf{not} finite! $\\square$")
        contradict_finish.scale(0.8)
        contradict_finish.next_to(contradict, RIGHT)
        self.play(Write(contradict_finish))
        self.wait()

        self.play(FadeOut(game_tree), FadeOut(turn_counter))
        self.wait()

        self.wait()

    def define_game(self):
        # Construct game tree
        game_tree = GameTree(3, layer_widths=[4.0])
        game_tree.show_creation(self, slow_anim=True)
        self.wait(20)

        chessboards = []
        for pos in game_tree.positions:
            chessboard = Chessboard()
            chessboard.scale(radius_of(pos.shape) / 7.0)
            chessboard.move_to(pos.shape)
            self.play(FadeIn(chessboard))
            chessboards.append(chessboard)

        turn_labels = game_tree.show_player_turns(self, slow_anim=True)
        self.wait(20)

        self.play(*[ FadeOut(board) for board in chessboards ])
        self.wait(2)

        position_labels = game_tree.label_positions(self, slow_anim=True)
        self.wait(10)

        self.play(FadeOut(game_tree), *[ FadeOut(label) for label in turn_labels ], *[ FadeOut(label) for label in position_labels])
        self.wait()

    def define_determined(self):
        # Construct game tree
        game_tree = GameTree(3)
        game_tree.show_creation(self, slow_anim=True)
        turn_labels = game_tree.show_player_turns(self)
        self.wait()
        position_labels = game_tree.label_positions(self)
        self.wait()

        # Randomly partition the ending positions
        for pos in game_tree.layers[-1]:
            pos.with_player1_wins(random.random() < 0.5)

        self.play(*[ anim for pos in game_tree.layers[-1] for anim in pos.winner_anims()])
        self.wait()

        # Introduce winning positions
        # First, what it means to be a winning position for player 1
        self.play(ApplyMethod(game_tree.starting_position.set_color, PLAYER_ONE_COLOR))
        self.wait(10)

        self.play(ApplyMethod(game_tree.starting_position.set_color, WHITE))
        self.wait()

        # Then for player 2
        self.play(ApplyMethod(game_tree.starting_position.set_color, PLAYER_TWO_COLOR))
        self.wait(10)

        self.play(ApplyMethod(game_tree.starting_position.set_color, WHITE))
        self.wait()

        # Solve the game
        game_tree.solve()
        game_tree.show_solving(self, slow_anim=True)
        self.wait(10)

        self.play(FadeOut(game_tree), *[ FadeOut(label) for label in turn_labels], *[ FadeOut(label) for label in position_labels ])
        self.wait()

        # Show another game
        game_tree = GameTree(6)
        game_tree.show_creation(self)
        turn_labels = game_tree.show_player_turns(self)
        self.wait()

        for pos in game_tree.layers[-1]:
            pos.with_player1_wins(random.random() < 0.5)

        # Solve the game
        game_tree.solve()
        game_tree.show_solving(self)
        self.wait(10)

        self.play(FadeOut(game_tree), *[ FadeOut(label) for label in turn_labels])
        self.wait()

    def write_text_with_element(self, position_first, *items, positioning=RIGHT):
        anims = []

        res_items = []
        prev_item = None
        old_pos = None
        new_pos = None

        for item_content in items:
            if isinstance(item_content, str):
                item = TextMobject(item_content)
            else:
                item = copy.deepcopy(item_content)

                if isinstance(item_content, Element):
                    item.ready(False)

            if prev_item is None:
                old_pos = item.get_center()
                position_first(item)
            else:
                if isinstance(prev_item, TextMobject):
                    old_pos = item.get_center()
                    item.next_to(prev_item, positioning)
                    anims.append(Write(prev_item))
                else:
                    new_pos = prev_item.get_center()
                    old_old_pos = old_pos

                    old_pos = item.get_center()
                    item.next_to(prev_item, positioning)

                    prev_item.move_to(old_old_pos)
                    anims.append(ApplyMethod(prev_item.move_to, new_pos))

            prev_item = item
            res_items.append(item)

        # If there were no items.
        if prev_item is None:
            return VGroup()

        # Add the animation for the last item in the group.
        if isinstance(prev_item, TextMobject):
            anims.append(Write(prev_item))
        else:
            new_pos = prev_item.get_center()
            prev_item.move_to(old_pos)
            anims.append(ApplyMethod(prev_item.move_to, new_pos))

        self.play(*anims)

        return VGroup(*res_items)

    def theorem_text(self, text, theorem_type="Theorem"):
        if theorem_type is None:
            return TextMobject(text)
        else:
            return TextMobject("\\textbf{{\\underline{{{}}}}}: ".format(theorem_type), text)

    def refine_text(self, old_text_obj, new_text, theorem_type=None, position=UP + LEFT):
        new_text_obj = self.theorem_text(new_text, theorem_type=theorem_type)

        if position is not None:
            new_text_obj.to_corner(position)
        else:
            new_text_obj.move_to(old_text_obj)

        self.play(Transform(old_text_obj, new_text_obj))
        self.wait()

    def write_theorem(self, text, theorem_type="Theorem"):
        thm = self.theorem_text(text, theorem_type=theorem_type)
        thm.to_corner(UP + LEFT)
        self.play(Write(thm))
        self.wait()

        return thm

    def introduce_theorem(self, text, theorem_type="Theorem"):
        thm = self.theorem_text(text, theorem_type=theorem_type)
        self.play(Write(thm))
        self.wait()

        self.play(ApplyMethod(thm.to_corner, UP + LEFT))
        self.wait()

        return thm

    def introduce_statement(self, name, text):
        axiom = TextMobject(text)
        self.play(Write(axiom))
        self.wait()

        self.play(ApplyMethod(axiom.to_corner, UP + RIGHT))
        self.wait()

        axiom_name = TextMobject('\\underline{{{}}}:'.format(name))
        axiom_name.add_updater(lambda self: self.next_to(axiom, LEFT))
        self.play(Write(axiom_name))
        self.wait()

        return axiom_name, axiom

