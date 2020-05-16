#!/usr/bin/env python

from manimlib.imports import *

import itertools as it

# From: https://stackoverflow.com/a/1482316/1498618
def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return list(it.chain.from_iterable(it.combinations(s, r) for r in range(len(s)+1)))

class Element(SmallDot):
    def __init__(self, parent, color):
        super().__init__()

        self.parent = parent
        self.color = color

        self.speed = 0.75
        self.dir = random.uniform(0, 2*PI)

        self.is_ready = True

        self.set_color(self.color)

        self.anchor_to(self.parent)
        self.move_to(self.reposition())

    def ready(self, val=True):
        self.is_ready = val
        return self

    def anchor_to(self, new_parent):
        self.parent = new_parent

        self.clear_updaters()
        self.add_updater(lambda self, dt: self.update_position(dt))

        return self

    def reposition(self):
        offset_angle = random.uniform(0, 2*PI)
        offset_radius = random.uniform(0, 1)

        # Use 2.2 so we don't get too close to the boundary.
        return np.array([offset_radius * math.cos(offset_angle) * self.parent.get_width() / 2.2 + self.parent.get_x(),
                         offset_radius * math.sin(offset_angle) * self.parent.get_height() / 2.2 + self.parent.get_y(), 0])

    def update_position(self, dt):
        if self.is_ready:
            new_x = self.get_x() + dt*self.speed*math.cos(self.dir)
            new_y = self.get_y() + dt*self.speed*math.sin(self.dir)

            i = 0
            while not self.in_parent(new_x, new_y) and i < 5:
                self.dir = random.uniform(0, 2*PI)

                new_x = self.get_x() + dt*self.speed*math.cos(self.dir)
                new_y = self.get_y() + dt*self.speed*math.sin(self.dir)

                i += 1

            if self.in_parent(new_x, new_y):
                self.move_to(np.array([new_x, new_y, 0]))

        return self

    def in_parent(self, new_x, new_y):
        pt = np.array([new_x, new_y, 0])

        # Note, this is also intended to work for ellipses.
        if isinstance(self.parent, Circle):
            center = self.parent.get_center()
            radius_x = self.parent.get_width() / 2.0
            radius_y = self.parent.get_height() / 2.0

            radii = np.array([radius_x, radius_y, 1])

            return np.linalg.norm((pt - center) / radii) < 0.95
        else:
            return True

class Set:
    def __init__(self, shape=None, name=None, color=None):
        self.obj = None
        self.shape = shape
        self.elements = []
        self.name = name
        self.name_obj = None
        self.color = color if color is not None else WHITE
        self.faded_obj = False

    def get_obj(self):
        return self.obj

    def get_shape(self):
        return self.shape

    def get_elements(self):
        return self.elements

    def change_name(self, new_name):
        anims = []
        self.name = new_name

        if self.name_obj is None:
            self.name_obj = TexMobject(self.name)
            self.name_obj.add_updater(lambda nm: nm.next_to(self.shape, DOWN))
            self.name_obj.set_color(self.color)
            anims.append(Write(self.name_obj))

            self.obj = VGroup(self.shape, self.name_obj)
        else:
            new_name_obj = TexMobject(self.name)
            new_name_obj.set_color(self.color)
            new_name_obj.next_to(self.shape, DOWN)

            anims.append(Transform(self.name_obj, new_name_obj))

        return anims

    def conjure_shape(self, adjustment=None):
        anims = []
        if self.shape is None:
            self.shape = Circle()
            self.shape.set_stroke(self.color)

        self.shape.scale(0.0005)

        bigger_shape = copy.deepcopy(self.shape)
        bigger_shape.scale(1 / 0.0005)

        if adjustment is not None:
            adjustment(self.shape)
            adjustment(bigger_shape)

        anims.append(Transform(self.shape, bigger_shape))

        if self.name is not None:
            anims.extend(self.change_name(self.name))
        else:
            self.obj = self.shape

        return anims

    def conjure_elements(self, element_num=None, element_colors=None, elements=None):
        if element_num is not None:
            return self.make_elements(element_num)
        elif element_colors is not None:
            return self.make_elements_colored(element_colors)
        elif elements is not None:
            return self.add_elements(elements)

        return []

    def conjure(self, adjustment=None, element_num=None, element_colors=None, elements=None):
        return self.conjure_shape(adjustment=adjustment) + self.conjure_elements(element_num=element_num, element_colors=element_colors, elements=elements)

    def add_elements(self, new_elements):
        anims = []

        for e in new_elements:
            new_e = copy.deepcopy(e)
            new_e.anchor_to(self.shape)
            self.elements.append(new_e)

        return anims

    def take_elements(self, new_elements):
        for e in new_elements:
            e.anchor_to(self.shape)
            self.elements.append(e)

        return self

    def clear_elements(self):
        old_elements = self.elements
        self.elements = []
        return old_elements

    def make_elements_colored(self, colors):
        anims = []
        self.elements = []

        for color in colors:
            p = self.make_element()
            p.set_color(color)
            self.elements.append(p)

        anims.extend([ShowCreation(p) for p in self.elements])

        return anims

    def ready_elements(self):
        for p in self.elements:
            p.ready()
        return self

    def unready_elements(self):
        for p in self.elements:
            p.ready(False)
        return self

    def make_elements(self, num):
        anims = []
        self.elements = [self.make_element() for i in range(num)]
        anims.extend([ShowCreation(p) for p in self.elements])
        return anims

    def make_element(self):
        return Element(self.shape, self.color)

    def remove_element(self, elem):
        self.elements.remove(elem)
        return self

    def reposition_elements(self):
        anims = []

        for e in self.elements:
            new_pos = e.reposition()
            anims.append(ApplyMethod(e.move_to, new_pos))

        return anims

    def fade(self):
        to_fade = []
        if not self.faded_obj:
            self.obj.clear_updaters()
            to_fade.append(self.obj)
            self.faded_obj = True

        to_fade.extend(self.elements)
        return [FadeOut(o) for o in to_fade]

    def fade_obj(self):
        if self.faded_obj:
            return []
        else:
            self.faded_obj = True
            return [FadeOut(self.obj)]

class SetTheoryAxioms(Scene):
    def construct(self):
        title = TextMobject("Set Theory")
        self.play(Write(title))
        self.wait()
        self.play(FadeOut(title))

        self.show_axiom_existence()

        name, axiom_one = self.introduce_statement("Extensionality", "$\\forall X. \\forall Y. \\forall z. (z \\in X \\Leftrightarrow z \\in Y) \\Rightarrow X = Y$")

        colors = ['#D999FF', '#AC8BE8', '#ADA6FF', '#8B9CE8', '#99C6FF']
        set_x = Set(name="X")
        set_y = Set(name="Y")
        self.play(*(set_x.conjure(lambda s: s.move_to(3*LEFT), element_colors=colors) +
                    set_y.conjure(lambda s: s.move_to(3*RIGHT), element_colors=colors)))

        to_fade = []
        gs = []

        for ex, ey in zip(set_x.get_elements(), set_y.get_elements()):
            new_ex = copy.copy(ex)
            new_ey = copy.copy(ey)
            new_ex.clear_updaters()
            new_ey.clear_updaters()

            self.add(new_ex)
            self.add(new_ey)

            contain_x = TexMobject("\\in X")
            contain_x.move_to(LEFT)
            and_tex = TexMobject("\\land")
            contain_y = TexMobject("\\in Y")
            contain_y.move_to(RIGHT)
            self.play(Write(contain_x), Write(and_tex), Write(contain_y),
                      ApplyMethod(new_ex.next_to, contain_x, LEFT), ApplyMethod(new_ey.next_to, contain_y, LEFT))
            g = VGroup(and_tex, contain_x, contain_y, new_ex, new_ey)
            gs.append(g)
            self.play(*[ApplyMethod(e.shift, 0.5*UP) for e in gs])
            to_fade.append(g)

        self.wait()

        implies = TexMobject("\\Rightarrow")

        equality = TexMobject("X = Y")
        equality.move_to(0.5*DOWN)
        self.play(Write(implies), Write(equality))
        self.wait()
        self.wait()

        self.play(FadeOutAndShift(equality, DOWN), FadeOutAndShift(implies, DOWN),
                  FadeOutAndShift(axiom_one, UP), FadeOutAndShift(name, UP),
                  *[FadeOut(e) for e in to_fade],
                  *set_x.fade(),
                  *set_y.fade())
        self.wait()

        name, axiom_two = self.introduce_statement("Pairing", "$\\forall X. \\forall Y. \\exists Z. \\forall A. A \\in Z \\Leftrightarrow (A = X \\lor A = Y)$")

        set_x = Set(color=RED)
        set_y = Set(color=BLUE)
        self.play(*(set_x.conjure(lambda s: s.move_to(2*LEFT), element_num=10) +
                    set_y.conjure(lambda s: s.move_to(2*RIGHT), element_num=50)))
        self.wait()

        paired = self.pair([set_x, set_y], name="Z")
        self.wait()

        self.refine_text(axiom_two, "$\\forall X. \\forall Y. \\exists Z. Z = \{X, Y\}$", position=UP+RIGHT)

        self.play(FadeOutAndShift(name, UP), FadeOutAndShift(axiom_two, UP),
                  *paired.fade(), *set_x.fade(), *set_y.fade())
        self.wait()

        name, axiom_three = self.introduce_statement("Union", "$\\forall \\mathcal{C}. \\exists U. \\forall x. x \\in U \\Leftrightarrow \\exists A. A \\in \\mathcal{C} \\land x \\in A$")

        set_a = Set(color=RED)
        set_b = Set(color=BLUE)
        set_c = Set(color=GREEN)
        set_d = Set(color=PURPLE)

        self.play(*set_a.conjure(lambda s: s.move_to(1.1*UP), element_num=5))
        self.play(*set_b.conjure(lambda s: s.move_to(2*RIGHT), element_num=20))
        self.play(*set_c.conjure(lambda s: s.move_to(1.1*DOWN), element_num=60))
        self.play(*set_d.conjure(lambda s: s.move_to(2*LEFT), element_num=25))

        unioned = self.pair([set_a, set_b, set_c, set_d], name='\\mathcal{C}')
        self.union_col(unioned, [set_a, set_b, set_c, set_d], new_name='U')

        self.refine_text(axiom_three, "$\\forall \\mathcal{C}. \\exists U. U = \\bigcup \\mathcal{C}$", position=UP+RIGHT)

        self.play(FadeOutAndShift(name, UP), FadeOutAndShift(axiom_three, UP),
                  *unioned.fade())
        self.wait()

        name, axiom_four = self.introduce_statement("Powerset", "$\\forall X. \\exists P. \\forall A. A \\in P \\Leftrightarrow (\\forall y. y \\in A \\Rightarrow Y \\in X)$")

        set_x = Set(shape=Circle(radius=0.8, color=WHITE), color=WHITE, name='X')
        self.play(*set_x.conjure(element_colors=[RED,GREEN,BLUE,PURPLE]))
        self.wait()

        new_sets = []

        # Don't include the whole set.
        pset = [x for x in powerset(set_x.get_elements()) if len(x) < len(set_x.get_elements())]

        for i, es in enumerate(pset):
            new_set = Set()

            r = 2
            theta = i * 2 * PI / len(pset)

            offset_x = r * math.cos(theta)
            offset_y = r * math.sin(theta)
            offset = np.array([offset_x, offset_y, 0])

            anims = new_set.conjure(adjustment=lambda s: s.shift(set_x.get_shape().get_center() - s.get_center() + offset).scale(0.3), elements=es)
            anims.extend(new_set.reposition_elements())
            self.play(*anims)

            new_sets.append(new_set)

        pset_set = Set(shape=Circle(radius=2.75, color=WHITE), color=WHITE, name="P")
        self.play(*pset_set.conjure_shape())
        self.wait()

        self.refine_text(axiom_four, "$\\forall X. \\exists P. \\forall A. A \\in P \\Leftrightarrow A \\subseteq X$", position=UP+RIGHT)
        self.refine_text(axiom_four, "$\\forall X. \\exists P. P = \\mathcal{P}(X)$", position=UP+RIGHT)

        self.play(FadeOutAndShift(axiom_four, UP), FadeOutAndShift(name, UP),
                  *pset_set.fade(),
                  *[a for s in new_sets for a in s.fade()],
                  *set_x.fade())
        self.wait()

        name, axiom_compr = self.introduce_statement("Comprehension", "For any formula $\\varphi$, \\\\ $\\forall X. \\exists Y. \\forall a. a \\in Y \\Leftrightarrow (a \\in X \\land \\varphi(a))$")
        self.refine_text(axiom_compr, "For any formula $\\varphi$, $\\forall X. \\exists Y. Y = \\{ a \\in X : \\varphi(a) \\}$", position=UP + RIGHT)

        set_x = Set(shape=Circle(radius=2.5, color=WHITE), color=WHITE, name='X')
        self.play(*set_x.conjure(element_num=20))
        self.wait()

        self.comprehension(set_x, lambda elem: random.choice([True, False]), new_name='Y')
        self.wait(3)

        self.play(FadeOutAndShift(name, UP), FadeOutAndShift(axiom_compr, UP),
                  *set_x.fade())
        self.wait()

        empty_set_exists = self.introduce_theorem("The empty set exists; that is, $\\exists X. \\forall y. \\lnot(y \\in x)$")
        self.refine_text(empty_set_exists, "The empty set exists; that is, $\\exists X. \\forall y. y \\not\\in x$", theorem_type="Theorem")
        self.refine_text(empty_set_exists, "The empty set exists; that is, $\\exists X. X = \\emptyset$", theorem_type="Theorem")

        def_varphi = TextMobject("Let $\\varphi(a)$ be $a \\neq a$.")
        def_varphi.next_to(empty_set_exists, DOWN)
        def_varphi.shift(3.5*LEFT)
        self.play(Write(def_varphi))

        set_x = self.set_exists(rad=2.5)
        self.wait()

        self.comprehension(set_x, lambda x: False, new_name='\\emptyset')
        self.wait()

        self.play(FadeOutAndShift(empty_set_exists, UP),
                  FadeOutAndShift(def_varphi, LEFT),
                  *set_x.fade())
        self.wait()

        with open('formal_proof.txt') as f:
            contents = f.read()

        empty_set_exists = self.introduce_theorem("The empty set exists; that is, $\\exists X. \\forall y. \\lnot(y \\in x)$")
        self.wait()

        t = TexMobject(contents)
        t.scale(0.45)
        self.play(Write(t))
        self.wait(4)

        self.play(FadeOutAndShift(empty_set_exists, UP), FadeOutAndShift(t, DOWN))
        self.wait()

        union_two = self.introduce_theorem("The union of any two sets $A$ and $B$, written $A \\cup B$, \\\\ is a set.")
        set_a = Set(color=RED)
        set_b = Set(color=BLUE)

        self.play(*set_a.conjure(lambda s: s.move_to(1.5*LEFT), element_num=45))
        self.play(*set_b.conjure(lambda s: s.move_to(1.5*RIGHT), element_num=80))

        unioned = self.pair([set_a, set_b], name='\\{A, B\\}', height_padding=1.5)
        self.union_col(unioned, [set_a, set_b], new_name='A \\cup B')
        self.wait()

        self.play(FadeOutAndShift(union_two, UP),
                  *set_a.fade(), *set_b.fade(), *unioned.fade())
        self.wait()

        singletons = self.introduce_theorem("For any set $A$, the singleton $\\{A\\}$ is a set.")
        set_a = Set(color=RED)
        set_a_cpy = Set(color=RED)

        self.play(*set_a.conjure(lambda s: s.move_to(1.5*LEFT), element_num=45))
        self.play(*set_a_cpy.conjure(lambda s: s.move_to(1.5*RIGHT), element_num=45))

        paired = self.pair([set_a, set_a_cpy], name='\\{A\\}')
        self.wait()

        anims = []
        anims.append(ApplyMethod(set_a.get_shape().shift, 1.5*RIGHT))
        anims.append(ApplyMethod(set_a_cpy.get_shape().shift, 1.5*LEFT))
        self.play(*anims)

        anims = []
        anims.extend(set_a.reposition_elements())
        anims.extend(set_a_cpy.reposition_elements())
        self.play(*anims)

        self.play(*set_a_cpy.fade())
        self.wait()

        self.play(FadeOutAndShift(singletons, UP),
                  *set_a.fade(), *paired.fade())
        self.wait()

        pair_def = self.introduce_theorem("$(x,y) = \\{\\{x\\}, \\{x,y\\}\\}$", theorem_type="Definition")

        set_a = Set(color=RED)
        set_b = Set(color=BLUE)

        self.play(*set_a.conjure(lambda s: s.move_to(RIGHT), element_num=60))
        self.play(*set_b.conjure(lambda s: s.move_to(3.5*RIGHT), element_num=3))

        pair_right = self.pair([set_a, set_b], name='\\{A,B\\}')
        self.wait()

        set_a_cpy = Set(color=RED)
        self.play(*set_a_cpy.conjure(lambda s: s.move_to(3.5*LEFT), element_num=60))
        self.wait()

        pair_left = self.pair([set_a_cpy], name='\\{A\\}', width_padding=0)
        self.wait()

        ordered_pair = self.pair([pair_left, pair_right], name='(A,B)', height_padding=2.75)
        self.wait()

        self.play(FadeOutAndShift(pair_def, UP),
                  *set_a_cpy.fade(), *set_a.fade(), *set_b.fade(), *pair_right.fade(), *pair_left.fade(), *ordered_pair.fade())
        self.wait()

    def show_axiom_existence(self):
        name, axiom_zero = self.introduce_statement("Existence", "$\\exists X. X = X$")

        ax0_set = self.set_exists()
        self.wait()

        self.play(FadeOutAndShift(axiom_zero, UP),
                  FadeOutAndShift(name, UP),
                  *ax0_set.fade())
        self.wait()

    def pair(self, sets, name=None, height_padding=1, width_padding=1):
        center_of_mass = np.array([0.0,0.0,0.0])
        min_x = 0
        max_x = 0
        min_y = 0
        max_y = 0

        for s in sets:
            center_of_mass += s.get_shape().get_center()
            x_low = s.get_shape().get_x() - s.get_shape().get_width() / 2.0
            x_high = s.get_shape().get_x() + s.get_shape().get_width() / 2.0

            y_low = s.get_shape().get_y() - s.get_shape().get_height() / 2.0
            y_high = s.get_shape().get_y() + s.get_shape().get_height() / 2.0

            min_x = min(x_low, min_x)
            max_x = max(x_high, max_x)

            min_y = min(y_low, min_y)
            max_y = max(y_high, max_y)

        center_of_mass = center_of_mass / len(sets)

        paired = Set(shape=Ellipse(width=max_x - min_x + width_padding, height=max_y - min_y + height_padding, color=WHITE), color=WHITE, name=name)
        self.play(*paired.conjure_shape(adjustment=lambda s: s.move_to(center_of_mass)))

        return paired

    def union_col(self, col, sets, new_name=None):
        anims = []
        for s in sets:
            col.take_elements(s.clear_elements())
            anims.extend(s.fade())

        self.play(*anims)

        if new_name is not None:
            self.play(*col.change_name(new_name))

        return col

    def union(self, sets, name=None, height_padding=0.5, width_padding=0.5):
        unioned = self.pair(sets,name=name,height_padding=height_padding,width_padding=width_padding)
        return self.union_col(unioned, sets)

    def set_exists(self, rad=1):
        ax0_set = Set(shape=Circle(radius=rad, color=WHITE))
        self.play(*ax0_set.conjure(element_num=20))
        return ax0_set

    def comprehension(self, set_x, pred, new_name=None):
        anims = []
        to_fade = []
        to_remove = []

        self.play(*set_x.reposition_elements())

        set_x.unready_elements()

        for elem in set_x.get_elements():
            varphi = TexMobject("\\varphi(")
            close_paren = TexMobject(")")

            to_fade.append(varphi)
            to_fade.append(close_paren)

            varphi.next_to(elem, 0.1*LEFT)
            close_paren.next_to(elem, 0.1*RIGHT)

            if pred(elem):
                varphi.set_color(GREEN)
                close_paren.set_color(GREEN)
            else:
                varphi.set_color(RED)
                close_paren.set_color(RED)
                to_remove.append(elem)

            anims.append(Write(varphi))
            anims.append(Write(close_paren))

        self.play(*anims)
        self.wait()

        for elem in to_remove:
            set_x.remove_element(elem)

        self.play(*[FadeOut(o) for o in to_fade + to_remove])
        if new_name is not None:
            self.play(*set_x.change_name(new_name))
        self.wait()

        set_x.ready_elements()

    def refine_text(self, old_text_obj, new_text, theorem_type=None, position=UP + LEFT):
        if theorem_type is None:
            new_text_obj = TextMobject(new_text)
        else:
            new_text_obj = TextMobject("\\textbf{{\\underline{{{}}}}}: {}".format(theorem_type, new_text))

        new_text_obj.to_corner(position)
        self.play(Transform(old_text_obj, new_text_obj))
        self.wait()

    def introduce_theorem(self, text, theorem_type="Theorem"):
        thm = TextMobject("\\textbf{{\\underline{{{}}}}}: {}".format(theorem_type, text))
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

