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

class GameTreePosition(VGroup):
    def __init__(self, shape, parent):
        super().__init__(shape)
        self.shape = shape
        self.parent = parent
        self.children = []

    def add_child(self, child):
        self.children.append(child)

    def creation_anims(self):
        if self.parent is None:
            self.parent_edge = None
            return [ ShowCreation(self.shape) ]
        else:
            self.parent_edge = Line(self.parent.shape, self.shape)
            return [ ShowCreation(self.shape), ShowCreation(self.parent_edge) ]

class GameTree:
    def __init__(self, depth):
        self.layers = []

        self.starting_position = GameTreePosition(Circle(color=WHITE), None)
        self.starting_position.scale(0.5)
        self.starting_position.shift(3*UP)

        self.layers.append([self.starting_position])

        layer_widths = [7.5]
        for i in range(depth):
            new_layer = []
            for pos in self.layers[-1]:
                layer_width = layer_widths.pop(0)
                child_num = random.randint(1, 3)
                new_layer += self.draw_position_layer(pos, child_num, layer_width=layer_width)
                for j in range(child_num):
                    layer_widths.append(layer_width / (child_num + 0.5))
            self.layers.append(new_layer)

    def draw_position_layer(self, parent, num, layer_width=6, shape_gen=lambda size: Circle(color=WHITE).scale(size)):
        if num == 1:
            radius = radius_of(parent) * 0.8
        else:
            radius = min(radius_of(parent) * 0.8, 0.5 * layer_width / (1.5 * (num - 1)))

        new_positions = []
        for i in range(num):
            pos = GameTreePosition(shape_gen(radius), parent)
            parent.add_child(pos)
            pos.next_to(parent, 1.3*DOWN)
            if num > 1:
                pos.shift(0.5*layer_width*LEFT)
                pos.shift(layer_width/(num - 1)*i*RIGHT)

            new_positions.append(pos)

        return new_positions

    def show_creation(self, scene):
        for layer in self.layers:
            anims = []

            for pos in layer:
                anims += pos.creation_anims()

            scene.play(*anims)
            scene.wait()

class GamesDetermined(Scene):
    def construct(self):
        # title = TextMobject("Who wins in Chess?")
        # self.play(Write(title))
        # self.wait()

        # subtitle = TextMobject("why all finite games are determined")
        # subtitle.scale(0.5)
        # subtitle.next_to(title, DOWN)
        # self.play(Write(subtitle))
        # self.wait()

        # self.play(FadeOut(title), FadeOut(subtitle))
        # self.wait()

        self.show_proof()

    def show_proof(self):
        # Construct game tree
        game_tree = GameTree(4)
        starting_position = game_tree.starting_position

        game_tree.show_creation(self)

        # Randomly partition the ending positions
        winning_for_p1 = []
        winning_for_p2 = []

        anims = []
        for pos in game_tree.layers[-1]:
            if random.random() < 0.5:
                winning_for_p1.append(pos)
                anims.append(ApplyMethod(pos.set_color, RED))
            else:
                winning_for_p2.append(pos)
                anims.append(ApplyMethod(pos.set_color, BLUE))

        self.play(*anims)
        self.wait()

        # Introduce winning positions

        # First, what it means to be a winning position for RED
        self.play(ApplyMethod(starting_position.set_color, RED))
        self.wait()

        self.play(ApplyMethod(starting_position.set_color, WHITE))
        self.wait()

        self.play(ApplyMethod(starting_position.set_color, BLUE))
        self.wait()

        self.play(ApplyMethod(starting_position.set_color, WHITE))
        self.wait()

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

