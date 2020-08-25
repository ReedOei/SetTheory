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

class GamesDetermined(Scene):
    def construct(self):
        # TODO: Look into better transformations between text so that only the changing things look like they change.
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
        starting_position = Circle(color=WHITE)
        starting_position.scale(0.5)
        starting_position.shift(3*UP)
        self.play(ShowCreation(starting_position))
        self.wait()

        anims = []
        second_layer, anims = self.draw_position_layer(starting_position, 2, spacing=3.5)
        self.play(*anims)
        self.wait()

        anims = []
        third_layer = []
        for pos in second_layer:
            new_positions, new_anims = self.draw_position_layer(pos, 3, spacing=2.5)
            third_layer.extend(new_positions)
            anims.extend(new_anims)
        self.play(*anims)
        self.wait()

        anims = []
        fourth_layer = []
        for pos in third_layer:
            new_positions, new_anims = self.draw_position_layer(pos, 3, spacing=0.9, shape_gen=lambda size: TextMobject("\\vdots"))
            fourth_layer.extend(new_positions)
            anims.extend(new_anims)
        self.play(*anims)
        self.wait()

        anims = []
        final_layer = []
        for pos in fourth_layer:
            new_position, new_anims = self.draw_position_layer(pos, 2, spacing=0.8)
            final_layer.extend(new_positions)
            anims.extend(new_anims)
        self.play(*anims)
        self.wait()

        self.wait()

    def radius_of(self, obj):
        return 0.5 * 0.5 * (obj.get_width() + obj.get_height())

    def draw_position_layer(self, parent, num, spacing=1.5, shape_gen=lambda size: Circle(color=WHITE).scale(size)):
        # Half of the radius of the parent
        layer_width = self.radius_of(parent) * 4 * spacing
        radius = min(self.radius_of(parent) * 0.9, 0.5 * layer_width / (1.5 * (num - 1)))

        anims = []
        new_positions = []
        for i in range(num):
            pos = shape_gen(radius)
            pos.next_to(parent, 1.3*DOWN)
            pos.shift(0.5*layer_width*LEFT)
            pos.shift(layer_width/(num - 1)*i*RIGHT)
            anims.append(ShowCreation(pos))

            new_positions.append(pos)

            move = Line(parent, pos)
            anims.append(ShowCreation(move))

        return new_positions, anims

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

