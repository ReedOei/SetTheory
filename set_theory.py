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

        self.set_color(self.color)

        self.is_ready = False
        self.radii = None

        self.anchor_to(self.parent)
        self.move_to(self.reposition())

        self.speed = 0.5*np.mean(self.radii)
        self.dir = random.uniform(0, 2*PI)
        self.is_ready = True

    def ready(self, val=True):
        self.is_ready = val
        return self

    def anchor_to(self, new_parent):
        self.parent = new_parent
        self.update_radii()

        self.clear_updaters()
        self.add_updater(lambda self, dt: self.update_position(dt))

        return self

    def update_radii(self):
        # NOTE: This will only work for circles or ellipses.
        center = self.parent.get_center()
        radius_x = (self.parent.get_width() - self.get_width()) / 2.0
        radius_y = (self.parent.get_height() - self.get_height()) / 2.0
        self.radii = np.array([radius_x, radius_y, 1])

        return self

    def reposition(self, angle=None):
        if angle is None:
            offset_angle = random.uniform(0, 2*PI)
            offset_radius = random.uniform(0, 1) * 0.95 # Make sure we don't end up outside self.parent
        else:
            offset_angle = angle
            offset_radius = 0.5

        # Use 2.2 so we don't get too close to the boundary.
        return np.array([offset_radius * math.cos(offset_angle) * self.radii[0] + self.parent.get_x(),
                         offset_radius * math.sin(offset_angle) * self.radii[1] + self.parent.get_y(), 0])

    def update_position(self, dt):
        if self.is_ready:
            for i in range(3):
                new_x = self.get_x() + dt*self.speed*math.cos(self.dir)
                new_y = self.get_y() + dt*self.speed*math.sin(self.dir)

                if self.in_parent(new_x, new_y):
                    self.move_to(np.array([new_x, new_y, 0]))
                    return self

                self.dir = random.uniform(0, 2*PI)

        return self

    def in_parent(self, new_x, new_y):
        if self.radii[0] == 0 or self.radii[1] == 0:
            return False
        else:
            pt = np.array([new_x, new_y, 0])

            t = (pt - self.parent.get_center()) / self.radii
            return np.dot(t, t) < 0.98**2

class Set(VGroup):
    def __init__(self, shape=None, name=None, color=None):
        self.obj = None
        self.shape = shape
        self.elements = []
        self.name_str = name
        self.name_obj = None
        self.color = color if color is not None else WHITE
        self.faded_obj = False

        if self.shape is None:
            self.shape = Circle()
            self.shape.set_stroke(self.color)

        super().__init__(self.shape, *self.elements)

        # NOTE: Currently unused.
        self.parent = None

    def get_obj(self):
        return self.obj

    def get_shape(self):
        return self.shape

    def get_elements(self):
        return self.elements

    def scale_elements_only(self, amount):
        for e in self.get_elements():
            if isinstance(e, Element):
                e.scale(amount)
            elif isinstance(e, Set):
                e.scale_elements_only(amount)

        return self

    def change_name(self, new_name):
        anims = []
        self.name_str = new_name

        if self.name_obj is None:
            self.name_obj = TexMobject(self.name_str)
            self.name_obj.add_updater(lambda nm: nm.next_to(self.shape, DOWN))
            self.name_obj.set_color(self.color)
            anims.append(Write(self.name_obj))

            self.obj = VGroup(self.shape, self.name_obj)
        else:
            new_name_obj = TexMobject(self.name_str)
            new_name_obj.set_color(self.color)
            new_name_obj.next_to(self.shape, DOWN)

            anims.append(Transform(self.name_obj, new_name_obj))

        return anims

    def conjure_shape(self, adjustment=None, use_scaling=True):
        anims = []
        if adjustment is not None:
            adjustment(self.shape)

        if use_scaling:
            self.shape.scale(0.0005)

            bigger_shape = copy.deepcopy(self.shape)
            bigger_shape.scale(1 / 0.0005)

            if adjustment is not None:
                adjustment(bigger_shape)

            anims.append(Transform(self.shape, bigger_shape))
        else:
            anims.append(ShowCreation(self.shape))

        if self.name_str is not None:
            anims.extend(self.change_name(self.name_str))
        else:
            self.obj = self.shape

        return anims

    def scale(self, *args, **kwargs):
        res = super().scale(*args, **kwargs)
        self.update_radii()
        return res

    def update_radii(self):
        for e in self.elements:
            e.update_radii()
        return self

    def conjure_elements(self, element_num=None, element_colors=None, elements=None):
        if element_num is not None:
            return self.make_elements(element_num)
        elif element_colors is not None:
            return self.make_elements_colored(element_colors)
        elif elements is not None:
            return self.add_elements(elements)

        return []

    def conjure(self, adjustment=None, element_num=None, element_colors=None, elements=None, use_scaling=True):
        return self.conjure_shape(adjustment=adjustment, use_scaling=use_scaling) + self.conjure_elements(element_num=element_num, element_colors=element_colors, elements=elements)

    def add_elements(self, new_elements):
        anims = []

        for e in new_elements:
            new_e = copy.deepcopy(e)
            new_e.anchor_to(self.shape)
            self.elements.append(new_e)

        super().__init__(self.shape, *self.elements)

        return anims

    def anchor_to(self, parent):
        self.parent = parent
        return self

    def take_elements(self, new_elements):
        for e in new_elements:
            e.anchor_to(self.shape)
            self.elements.append(e)

        super().__init__(self.shape, *self.elements)
        return self

    def clear_elements(self):
        old_elements = self.elements
        self.elements = []
        super().__init__(self.shape, *self.elements)
        return old_elements

    def make_elements_colored(self, colors):
        anims = []
        self.elements = []

        for color in colors:
            p = self.make_element(color=color)
            p.set_color(color)
            self.elements.append(p)

        anims.extend([ShowCreation(p) for p in self.elements])

        super().__init__(self.shape, *self.elements)
        return anims

    # For compatibility with Element
    def ready(self, is_ready=True):
        if is_ready:
            self.ready_elements()
        else:
            self.unready_elements()

        return self

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
        super().__init__(self.shape, *self.elements)
        return anims

    def make_element(self, color=None):
        return Element(self.shape, color if color is not None else self.color)

    def remove_element(self, elem):
        self.elements.remove(elem)
        super().__init__(self.shape, *self.elements)
        return self

    def reposition_elements(self, evenly=None):
        anims = []

        for i, e in enumerate(self.elements):
            if isinstance(e, Element):
                if evenly:
                    new_pos = e.reposition(angle=2*PI*float(i)/len(self.elements))
                else:
                    new_pos = e.reposition()
                anims.append(ApplyMethod(e.move_to, new_pos))
            elif isinstance(e, Set):
                orig_pos = e.get_shape().get_center()

                if evenly is not None:
                    offset_angle = 2*PI*float(i) / len(self.elements)
                    offset_radius = evenly
                else:
                    offset_angle = random.uniform(0, 2*PI)
                    offset_radius = random.uniform(0, 1)

                new_pos = np.array([offset_radius * math.cos(offset_angle) * (self.shape.get_width() - e.get_shape().get_width()) / 2 + self.shape.get_x(),
                                    offset_radius * math.sin(offset_angle) * (self.shape.get_height() - e.get_shape().get_height()) / 2 + self.shape.get_y(), 0])

                e.get_shape().move_to(new_pos)
                anims.extend(e.reposition_elements(evenly=evenly))
                e.get_shape().move_to(orig_pos)
                anims.append(ApplyMethod(e.get_shape().move_to, new_pos))

        return anims

    def fade_obj(self):
        if self.faded_obj:
            return []
        else:
            self.faded_obj = True
            return [FadeOut(self.obj)]

class SetTheoryAxioms(Scene):
    def construct(self):
        # title = TextMobject("Set Theory")
        # self.play(Write(title))
        # self.wait()
        # self.play(FadeOut(title))

        # self.show_axiom_existence()
        # self.show_axiom_extensionality()
        # self.show_axiom_pairing()
        # self.show_axiom_union()
        # self.show_axiom_powerset()
        # self.show_axiom_comprehension()

        # self.prove_empty_set_exists()
        # self.prove_empty_set_exists_formal()
        # self.prove_union_two_sets()
        # self.prove_singleton_exists()

        # self.define_ordered_pairs()
        self.define_cartesian_product()

    def define_ordered_pairs(self):
        pair_def = self.introduce_theorem("$(x,y) := \\{\\{x\\}, \\{x,y\\}\\}$", theorem_type="Definition")

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

    def define_cartesian_product(self):
        cart_prod_def = self.introduce_theorem("$$X \\times Y := \\{(x,y) : x \\in X \\land y \\in Y\\}$$", theorem_type="Definition")
        self.refine_text(cart_prod_def, "$$X \\times Y := $$ $$\\{(x,y) : x \\in X, y \\in Y\\}$$", theorem_type="Definition")
        self.refine_text(cart_prod_def, "$$X \\times Y := $$ $$\\{(x,y) : x \\in X, y \\in Y\\}$$???", theorem_type="Definition")
        self.refine_text(cart_prod_def, "$$X \\times Y := $$ $$\\{z \\in \\mathcal{P}(\\mathcal{P}(X \\cup Y)) : \\exists x. x \\in X \\land \\exists y. y \\in Y \\land z = (x, y)\\}$$", theorem_type="Definition")
        self.refine_text(cart_prod_def, "$$X \\times Y := $$ $$\\{z \\in \\mathcal{P}(\\mathcal{P}(X \\cup Y)) : \\exists x. x \\in X \\land \\exists y. y \\in Y \\land z = \\{\\{x\\}, \\{x,y\\}\\}\\}$$", theorem_type="Definition")
        self.refine_text(cart_prod_def, "$$X \\times Y := $$ $$\\{z \\in \\mathcal{P}(\\mathcal{P}(X \\cup Y)) : \\exists x. x \\in X \\land \\exists y. y \\in Y \\land z = (x,y)\\}$$", theorem_type="Definition")
        self.refine_text(cart_prod_def, "$$X \\times Y := \\{z \\in \\mathcal{P}(\\mathcal{P}(X \\cup Y)) : \\exists x \\in X. \\exists y \\in Y. z = (x,y)\\}$$", theorem_type="Definition")
        self.refine_text(cart_prod_def, "$$X \\times Y := \\{z \\in \\mathcal{P}(\\mathcal{P}(X \\cup Y)) : \\exists x \\in X, y \\in Y. z = (x,y)\\}$$", theorem_type="Definition")
        self.refine_text(cart_prod_def, "$$X \\times Y := \\{z \\in \\mathcal{P}(\\mathcal{P}(X \\cup Y)) : \\exists x \\in X, y \\in Y. z = (x,y)\\}$$", theorem_type=None)
        self.play(FadeOutAndShift(cart_prod_def, UP))
        self.wait()

        set_a = Set()
        set_b = Set()

        self.play(*set_a.conjure(lambda s: s.move_to(0.1*LEFT).scale(0.25), element_colors=[RED]))
        self.play(*set_b.conjure(lambda s: s.move_to(0.1*RIGHT).scale(0.25), element_colors=[GREEN, BLUE]))

        set_u = self.union([set_a, set_b], height_padding=0.1, width_padding=0.1)
        self.wait()
        psets = self.powerset(set_u, r=0.4, rad_scale=0.5)
        pset1 = self.pair(psets, height_padding=0.3, width_padding=0.3)
        self.wait()

        psets2 = self.powerset(pset1, r=3)
        pset2 = self.pair(psets2, height_padding=0.4, width_padding=0.4)

        def phi(s):
            if len(s.get_elements()) != 2:
                return False

            if len(s.get_elements()[0].get_elements()) != 1 or len(s.get_elements()[1].get_elements()) != 2:
                return False

            colors_fst = set()
            colors_fst.add(str(s.get_elements()[0].get_elements()[0].color).upper())

            colors_snd = set()
            colors_snd.add(str(s.get_elements()[1].get_elements()[0].color).upper())
            colors_snd.add(str(s.get_elements()[1].get_elements()[1].color).upper())

            if not RED.upper() in colors_snd:
                return False

            return colors_fst == {RED.upper()} and colors_snd <= {RED.upper(), BLUE.upper(), GREEN.upper()}

        self.comprehension(pset2, phi)
        self.wait()

        anims = []
        for e in pset2.get_elements():
            anims.append(ApplyMethod(e.scale, 2))

        pset2.scale_elements_only(0.5)
        self.play(*anims)
        self.play(*pset2.reposition_elements(evenly=0.5))
        self.wait()

        pset2.scale_elements_only(2)
        self.play(ApplyMethod(pset2.scale, 0.5))
        self.wait()

        cart_prod_def = self.write_theorem("$$X \\times Y := \\{z \\in \\mathcal{P}(\\mathcal{P}(X \\cup Y)) : \\exists x \\in X, y \\in Y. z = (x,y)\\}$$", theorem_type=None)
        self.wait()

        self.play(FadeOutAndShift(cart_prod_def, UP), FadeOut(pset2))
        self.wait()

    def prove_singleton_exists(self):
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

    def prove_union_two_sets(self):
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

    def prove_empty_set_exists(self):
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

    def prove_empty_set_exists_formal(self):
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

    # Yeah comprehension is an axiom schema not an axiom whatever.
    def show_axiom_comprehension(self):
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

    def show_axiom_union(self):
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

    def show_axiom_powerset(self):
        name, axiom_four = self.introduce_statement("Powerset", "$\\forall X. \\exists P. \\forall A. A \\in P \\Leftrightarrow (\\forall y. y \\in A \\Rightarrow Y \\in X)$")

        set_x = Set(shape=Circle(radius=0.8, color=WHITE), color=WHITE, name='X')
        self.play(*set_x.conjure(element_colors=[RED,GREEN,BLUE,PURPLE]))
        self.wait()

        new_sets = self.powerset(set_x, slow_anim=True)

        pset_set = self.pair(new_sets, name="P")

        self.refine_text(axiom_four, "$\\forall X. \\exists P. \\forall A. A \\in P \\Leftrightarrow A \\subseteq X$", position=UP+RIGHT)
        self.refine_text(axiom_four, "$\\forall X. \\exists P. P = \\mathcal{P}(X)$", position=UP+RIGHT)

        self.play(FadeOutAndShift(axiom_four, UP), FadeOutAndShift(name, UP),
                  *pset_set.fade(),
                  *[a for s in new_sets for a in s.fade()],
                  *set_x.fade())
        self.wait()

    def powerset(self, set_x, slow_anim=False, r=2, rad_scale=1):
        new_sets = []

        # Don't include the whole set.
        pset = [x for x in powerset(set_x.get_elements()) if len(x) < len(set_x.get_elements())]

        anims = []
        for i, es in enumerate(pset):
            theta = i * 2 * PI / len(pset)

            offset_x = r * math.cos(theta)
            offset_y = r * math.sin(theta)
            offset = np.array([offset_x, offset_y, 0])

            scaling = 2*PI*r*rad_scale / (2.2 * len(pset))
            are_elems = True

            for e in es:
                if not isinstance(e, Element):
                    are_elems = False
                    break

            width, height = self.calculate_size(es)

            if not are_elems:
                new_set = Set(shape=Ellipse(color=WHITE, width=width + 0.5*scaling, height=height + 0.5*scaling))
            else:
                new_set = Set(shape=Circle(radius=scaling, color=WHITE))

            if slow_anim:
                anims = new_set.conjure(adjustment=lambda s: s.shift(set_x.get_shape().get_center() - s.get_center() + offset), elements=es, use_scaling=False)
                anims.extend(new_set.reposition_elements(evenly=0.7))
                self.play(*anims)
            else:
                anims.extend(new_set.conjure(adjustment=lambda s: s.shift(set_x.get_shape().get_center() - s.get_center() + offset), elements=es, use_scaling=False))
                anims.extend(new_set.reposition_elements(evenly=0.7))

            new_sets.append(new_set)

        if not slow_anim:
            self.play(*anims)

        new_sets.append(set_x)
        return new_sets

    def show_axiom_existence(self):
        name, axiom_zero = self.introduce_statement("Existence", "$\\exists X. X = X$")

        ax0_set = self.set_exists()
        self.wait()

        self.play(FadeOutAndShift(axiom_zero, UP),
                  FadeOutAndShift(name, UP),
                  *ax0_set.fade())
        self.wait()

    def show_axiom_extensionality(self):
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

    def calculate_size(self, sets):
        min_x = 0
        max_x = 0
        min_y = 0
        max_y = 0

        for s in sets:
            if isinstance(s, Set):
                x_low = s.get_shape().get_x() - s.get_shape().get_width() / 2.0
                x_high = s.get_shape().get_x() + s.get_shape().get_width() / 2.0

                y_low = s.get_shape().get_y() - s.get_shape().get_height() / 2.0
                y_high = s.get_shape().get_y() + s.get_shape().get_height() / 2.0

                min_x = min(x_low, min_x)
                max_x = max(x_high, max_x)

                min_y = min(y_low, min_y)
                max_y = max(y_high, max_y)

        return max_x - min_x, max_y - min_y

    def pair(self, sets, name=None, height_padding=1, width_padding=1):
        center_of_mass = np.array([0.0,0.0,0.0])
        width, height = self.calculate_size(sets)

        for s in sets:
            center_of_mass += s.get_shape().get_center()

        center_of_mass = center_of_mass / len(sets)

        paired = Set(shape=Ellipse(width=width + width_padding, height=height + height_padding, color=WHITE), color=WHITE, name=name)
        self.play(*paired.conjure_shape(adjustment=lambda s: s.move_to(center_of_mass), use_scaling=False))

        paired.take_elements(sets)

        return paired

    def show_axiom_pairing(self):
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

    def union_col(self, col, new_name=None):
        anims = []

        old_elems = col.clear_elements()
        for s in old_elems:
            # TODO: What to do with elements? Do we even need to worry about this?
            if isinstance(s, Set):
                col.take_elements(s.clear_elements())
                anims.append(FadeOut(s))

        self.play(*anims)

        if new_name is not None:
            self.play(*col.change_name(new_name))

        return col

    def union(self, sets, name=None, height_padding=0.5, width_padding=0.5):
        unioned = self.pair(sets,name=name,height_padding=height_padding,width_padding=width_padding)
        return self.union_col(unioned)

    def set_exists(self, rad=1):
        ax0_set = Set(shape=Circle(radius=rad, color=WHITE))
        self.play(*ax0_set.conjure(element_num=20))
        return ax0_set

    def comprehension(self, set_x, pred, new_name=None):
        anims = []
        to_fade = []
        to_remove = []

        self.play(*set_x.reposition_elements(evenly=0.7))

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

        self.play(*set_x.reposition_elements(evenly=0.7))

        set_x.ready_elements()

    def theorem_text(self, text, theorem_type="Theorem"):
        if theorem_type is None:
            return TextMobject(text)
        else:
            return TextMobject("\\textbf{{\\underline{{{}}}}}: {}".format(theorem_type, text))

    def refine_text(self, old_text_obj, new_text, theorem_type=None, position=UP + LEFT):
        new_text_obj = self.theorem_text(new_text, theorem_type=theorem_type)

        new_text_obj.to_corner(position)
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

