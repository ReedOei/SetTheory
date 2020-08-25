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

class OrderedPair(VGroup):
    def __init__(self, items):
        self.items = []
        self.objs = []
        self.objs.append(TexMobject("("))

        for i, item in enumerate(items):
            self.items.append(copy.deepcopy(item))
            self.objs.append(self.items[-1])
            if i + 1 < len(items):
                self.objs.append(TexMobject(","))

        self.objs.append(TexMobject(")"))

        super().__init__(*self.objs)

        self.original_positions = []
        self.parent = None
        for item in self.items:
            self.original_positions.append(item.get_center())
            item.ready(False)
            item.anchor_to(self)

        self.arrange(RIGHT)

        self.uuid = str(uuid.uuid4())

    def create(self):
        anims = []
        i = 0
        for obj in self.objs:
            if obj in self.items:
                new_position = obj.get_center()
                obj.move_to(self.original_positions[i])
                anims.append(ApplyMethod(obj.move_to, new_position))
                i += 1
            else:
                anims.append(Write(obj))

        return anims

    def scale_elements_only(self, amount):
        for item in self.items:
            item.scale_elements_only(amount)

        return self

    def get_item(self, idx):
        return self.items[idx]

    def ready(self, is_ready=True):
        return self

    def anchor_to(self, parent):
        self.parent = parent
        self.update_radii()
        return self

    def update_radii(self):
        center = self.parent.get_center()
        radius_x = (self.parent.get_width() - self.get_width()) / 2.0
        radius_y = (self.parent.get_height() - self.get_height()) / 2.0
        self.radii = np.array([radius_x, radius_y, 1])

        return self

    def reposition(self, angle=None, offset_radius=0.5):
        self.update_radii()

        if angle is None:
            offset_angle = random.uniform(0, 2*PI)
            offset_radius = random.uniform(0, 1) * 0.95 # Make sure we don't end up outside self.parent
        else:
            offset_angle = angle

        return np.array([offset_radius * math.cos(offset_angle) * self.radii[0] + self.parent.get_x(),
                         offset_radius * math.sin(offset_angle) * self.radii[1] + self.parent.get_y(), 0])

    def get_shape(self):
        return self

    def to_fade(self):
        return self

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

        self.speed = 0.9*np.mean(self.radii)
        self.dir = random.uniform(0, 2*PI)
        self.is_ready = True

        self.uuid = str(uuid.uuid4())

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

    def reposition(self, angle=None, offset_radius=0.5):
        self.update_radii()

        if angle is None:
            offset_angle = random.uniform(0, 2*PI)
            offset_radius = random.uniform(0, 1) * 0.9 # Make sure we don't end up outside self.parent
        else:
            offset_angle = angle

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
            return np.dot(t, t) < 0.99**2

    def to_fade(self):
        return self

    def scale_elements_only(self, amount):
        return self.scale(amount)

class Set(VGroup):
    def __init__(self, shape=None, name=None, color=None):
        self.shape = shape
        self.elements = []
        self.name_str = name
        self.name_obj = None
        self.color = color if color is not None else WHITE

        if self.shape is None:
            self.shape = Circle()
            self.shape.set_stroke(self.color)

        super().__init__(self.shape, *self.elements)

        # NOTE: Currently unused.
        self.parent = None

        self.uuid = str(uuid.uuid4())

    def to_fade(self):
        if self.name_obj is not None:
            return VGroup(self.name_obj, self.shape, *[e.to_fade() for e in self.elements])
        else:
            return VGroup(self.shape, *[e.to_fade() for e in self.elements])

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
            elif isinstance(e, OrderedPair):
                e.scale_elements_only(amount)

        return self

    def change_name(self, new_name):
        anims = []

        if new_name is None:
            if self.name_obj is not None:
                anims.append(FadeOut(self.name_obj))
                self.name_obj = None
        else:
            self.name_str = new_name

            if self.name_obj is None:
                self.name_obj = TexMobject(self.name_str)
                self.name_obj.add_updater(lambda nm: nm.next_to(self.shape, DOWN))
                self.name_obj.set_color(self.color)
                anims.append(Write(self.name_obj))
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
            anims.append(ApplyMethod(self.shape.scale, 1/0.0005))
        else:
            anims.append(ShowCreation(self.shape))

        if self.name_str is not None:
            anims.extend(self.change_name(self.name_str))

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
            if isinstance(e, Set):
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
            else:
                if evenly is not None:
                    new_pos = e.reposition(angle=2*PI*float(i)/len(self.elements), offset_radius=evenly)
                else:
                    new_pos = e.reposition()
                anims.append(ApplyMethod(e.move_to, new_pos))

        return anims

    # A version of reposition_elements that doesn't generate animations and just does the repositioning.
    def do_reposition_elements(self, evenly=None):
        for i, e in enumerate(self.elements):
            if isinstance(e, Set):
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
            else:
                if evenly is not None:
                    new_pos = e.reposition(angle=2*PI*float(i)/len(self.elements), offset_radius=evenly)
                else:
                    new_pos = e.reposition()
                e.move_to(new_pos)

        return self

    def __getitem__(self, key):
        for e in self.get_elements():
            if e.uuid == key:
                return e

        return None

class Function:
    def __init__(self, dom, codom, mapping, arrows=None):
        self.dom = dom
        self.codom = codom

        if isinstance(mapping, dict):
            self.mapping = mapping
        else:
            self.mapping = {}

            for x in self.dom.get_elements():
                self.mapping[x.uuid] = mapping(x).uuid

        self.arrows = [] if arrows is None else arrows

    def visualize_function(self, scene, slow_anim=False):
        anims = []

        arrows = []
        for elem_x in self.dom.get_elements():
            elem_y = self.codom[self.mapping[elem_x.uuid]]
            arr = Arrow(elem_x, elem_y, stroke_width=2, tip_length=0.15)

            # Need to do this because Python's scoping is absolute nonsense...
            def f(x, y):
                def g(self):
                    return self.put_start_and_end_on(x.get_center(),y.get_center())
                return g

            arr.add_updater(f(elem_x, elem_y))
            arrows.append(arr)

            if slow_anim:
                scene.play(ShowCreation(arr))
            else:
                anims.append(ShowCreation(arr))

        if not slow_anim:
            scene.play(*anims)

        self.arrows = arrows

        return self

    def __getitem__(self, elem):
        return self.codom[self.mapping[elem.uuid]]

    def preimage(self, elem):
        res = []
        for xid, yid in self.mapping.items():
            if yid == elem.uuid:
                res.append(self.dom[xid])

        return res

    def to_fade(self):
        return VGroup(*self.arrows)

class SetTheoryAxioms(Scene):
    def construct(self):
        # # TODO: Look into better transformations between text so that only the changing things look like they change.
        # title = TextMobject("Set Theory")
        # self.play(Write(title))
        # self.wait()
        # self.play(FadeOut(title))

        # # TODO: Add some text highlighting stuff
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
        # self.define_cartesian_product()

        self.define_subsets()

        # self.define_relation()
        # self.relation_example_equality()

        # self.define_functions()
        # self.function_examples()
        # self.prove_set_of_functions_exists()

        # self.define_image()

        # self.define_onto()
        # self.define_one_to_one()

        # self.define_bijective()

        # TODO: Some animations looking at comparing the sizes of finite sets (because we don't even know if infinite sets exist yet)

        # TODO: Should we use theorem_type="Definition" or theorem_type=None by default for definitions?

        # self.define_successor()

        # self.axiom_infinity()

        # TODO: Not sure when these actually need to be defined, it's sort of just extra terminology with no need for the moment.
        # self.define_dom_codom()

    def define_successor(self):
        # TODO: FINISH THIS
        # NOTE: The motivation for the successor is, at first, that we want to have a function that gives a different answer every time we apply it (i.e., never loops), and also works on arbitrary sets, because that's all we have.
        #       So then the reason we pick this function is that we know that a set will never be an element of itself, and we "remember" allt he previous sets by sticking them in there (i.e., the right operand of the union)
        #       Later, we'll see it plays nicely with ordinals too.
        successor_def = self.introduce_theorem("The \\emph{successor} of a set $X$ is $\\mathcal{S}(X) := X \\cup \\{ X \\}$", theorem_type="Def.")
        self.wait()

    def define_onto(self):
        onto_def = self.introduce_theorem("$f : X \\to Y$ is \\emph{onto} if its image is $Y$.", theorem_type="Definition")
        self.wait()

        set_x = Set(name="X", color=GREEN)
        set_y = Set(name="Y", color=WHITE)

        self.play(*set_x.conjure(lambda s: s.move_to(2.5*LEFT).scale(2), element_num=10), *set_y.conjure(lambda s: s.move_to(2.5*RIGHT).scale(2), element_num=6))
        self.play(*set_x.reposition_elements(), *set_y.reposition_elements())
        self.wait()

        func = self.arbitrary_function(set_x, set_y, is_onto=True)
        self.wait(2)

        for y in set_y.get_elements():
            xs = func.preimage(y)
            self.play(*[ApplyMethod(x.scale, 3) for x in xs], ApplyMethod(y.scale, 3))
            for x in xs:
                x.update_radii()
            y.update_radii()
            self.play(*[ApplyMethod(x.set_color, LAVENDER_ISH) for x in xs], ApplyMethod(y.set_color, YELLOW))
            self.wait()

            self.play(*[ApplyMethod(x.set_color, GREEN) for x in xs], ApplyMethod(y.set_color, WHITE))
            self.play(*[ApplyMethod(x.scale, 1/3) for x in xs], ApplyMethod(y.scale, 1/3))
            for x in xs:
                x.update_radii()
            y.update_radii()

        self.play(FadeOutAndShift(onto_def, UP),
                  FadeOut(set_x.to_fade()), FadeOut(set_y.to_fade()),
                  FadeOut(func.to_fade()))
        self.wait()

    def define_one_to_one(self):
        one_to_one_def = self.introduce_theorem("$f : X \\to Y$ is \\emph{one-to-one} if distinct elements are \\\\ mapped to distinct elements.", theorem_type="Definition")
        self.wait()

        self.refine_text(one_to_one_def, "$f : X \\to Y$ is \\emph{one-to-one} if whenever $x \\neq y$, \\\\ then $f(x) \\neq f(y)$.", theorem_type="Definition")
        self.wait()

        self.refine_text(one_to_one_def, "$f : X \\to Y$ is \\emph{one-to-one} if $f(x) = f(y)$ only when $x = y$.", theorem_type=None)
        self.wait()

        set_x = Set(name="X", color=GREEN)
        set_y = Set(name="Y", color=WHITE)

        self.play(*set_x.conjure(lambda s: s.move_to(2.5*LEFT).scale(2), element_num=3), *set_y.conjure(lambda s: s.move_to(2.5*RIGHT).scale(2), element_num=6))
        self.play(*set_x.reposition_elements(), *set_y.reposition_elements())
        self.wait()

        func = self.arbitrary_function(set_x, set_y, is_one_to_one=True)
        self.wait()

        self.play(FadeOutAndShift(one_to_one_def, UP),
                  FadeOut(set_x.to_fade()), FadeOut(set_y.to_fade()),
                  FadeOut(func.to_fade()))
        self.wait()

    def define_bijective(self):
        bij_def = self.introduce_theorem("$f : X \\to Y$ is \\emph{bijective} if it is one-to-one and onto.", theorem_type="Definition")
        self.wait()

        set_x = Set(name="X", color=GREEN)
        set_y = Set(name="Y", color=WHITE)

        self.play(*set_x.conjure(lambda s: s.move_to(2.5*LEFT).scale(2), element_num=6), *set_y.conjure(lambda s: s.move_to(2.5*RIGHT).scale(2), element_num=6))
        self.play(*set_x.reposition_elements(), *set_y.reposition_elements())
        self.wait()

        func = self.arbitrary_function(set_x, set_y, is_one_to_one=True, is_onto=True)
        self.wait(2)

        set_x.unready_elements()
        set_y.unready_elements()
        self.play(*set_x.reposition_elements(evenly=0.7), *set_y.reposition_elements(evenly=0.7))
        self.wait()

        for y in set_y.get_elements():
            xs = func.preimage(y)
            self.play(*[ApplyMethod(x.scale, 3) for x in xs], ApplyMethod(y.scale, 3))
            for x in xs:
                x.update_radii()
            y.update_radii()
            self.play(*[ApplyMethod(x.set_color, LAVENDER_ISH) for x in xs], ApplyMethod(y.set_color, YELLOW))
            self.wait()

            self.play(*[ApplyMethod(x.set_color, GREEN) for x in xs], ApplyMethod(y.set_color, WHITE))
            self.play(*[ApplyMethod(x.scale, 1/3) for x in xs], ApplyMethod(y.scale, 1/3))
            for x in xs:
                x.update_radii()
            y.update_radii()

        self.play(FadeOutAndShift(bij_def, UP),
                  FadeOut(set_x.to_fade()), FadeOut(set_y.to_fade()),
                  FadeOut(func.to_fade()))
        self.wait()

    def define_image(self):
        image_def = self.introduce_theorem("The \\emph{image} of $f : X \\to Y$ on $A \\subseteq X$ is $$f(A) := \\{y \\in Y : \\exists a \\in A. f(a) = y \\}$$", theorem_type="Definition")
        self.wait()

        self.refine_text(image_def, "$f(A) := \\{y \\in Y : \\exists a \\in A. f(a) = y \\}$", theorem_type="Definition")
        self.wait()

        set_x = Set(name="X", color=GREEN)
        set_y = Set(name="Y", color=WHITE)

        self.play(*set_x.conjure(lambda s: s.move_to(2.5*LEFT).scale(2), element_num=8), *set_y.conjure(lambda s: s.move_to(2.5*RIGHT).scale(2), element_num=20))
        self.play(*set_x.reposition_elements(), *set_y.reposition_elements())
        self.wait()

        func = self.arbitrary_function(set_x, set_y)
        self.wait()

        subset = random.sample(set_x.get_elements(), 4)
        self.highlight_subset(subset, color=LAVENDER_ISH)

        subset_im = [func[e] for e in subset]
        self.highlight_subset(subset_im, color=YELLOW)

        # NOTE: Have to include a phantom end curly bracket } for some reason. Unclear why....
        dom_set = self.write_text_with_element(lambda it: it.to_corner(DOWN + LEFT), "$A = \\left\\{\\phantom{\\}}$", *intersperse("$,$", subset), "$\\phantom{\\{}\\right\\}$")
        self.wait()

        im_set = self.write_text_with_element(lambda it: it.to_corner(DOWN + RIGHT).shift(3*LEFT), "$f(A) = \\left\\{\\phantom{\\}}$", *intersperse("$,$", subset_im), "$\\phantom{\\{}\\right\\}$")
        self.wait()

        self.play(FadeOutAndShift(image_def, UP),
                  FadeOut(set_x.to_fade()), FadeOut(set_y.to_fade()),
                  FadeOutAndShift(dom_set, LEFT), FadeOutAndShift(im_set, RIGHT),
                  FadeOut(func.to_fade()))
        self.wait()

        image_def = self.introduce_theorem("The \\emph{image} of $f : X \\to Y$ is $\\text{im}(f) := f(X)$", theorem_type="Definition")
        self.wait()

        set_x = Set(name="X", color=GREEN)
        set_y = Set(name="Y", color=WHITE)

        self.play(*set_x.conjure(lambda s: s.move_to(2.5*LEFT).scale(2), element_num=8), *set_y.conjure(lambda s: s.move_to(2.5*RIGHT).scale(2), element_num=20))
        self.play(*set_x.reposition_elements(), *set_y.reposition_elements())
        self.wait()

        func = self.arbitrary_function(set_x, set_y)
        self.wait()

        subset = set_x.get_elements()
        self.highlight_subset(subset, color=LAVENDER_ISH)

        subset_im = [func[e] for e in subset]
        self.highlight_subset(subset_im, color=YELLOW)

        im_set = self.write_text_with_element(lambda it: it.to_edge(DOWN).shift(4*LEFT), "$\\text{im}(f) = f(X) = \\left\\{\\phantom{\\}}$", *intersperse("$,$", subset_im), "$\\phantom{\\{}\\right\\}$")
        self.wait()

        self.play(FadeOutAndShift(image_def, UP),
                  FadeOut(set_x.to_fade()), FadeOut(set_y.to_fade()),
                  FadeOutAndShift(im_set, DOWN),
                  FadeOut(func.to_fade()))
        self.wait()

    def highlight_subset(self, subset, color=None):
        anims = []
        for elem in subset:
            anims.append(ApplyMethod(elem.scale, 2))
            elem.update_radii()
        self.play(*anims)
        self.wait()

        if color is not None:
            anims = []
            for elem in subset:
                anims.append(ApplyMethod(elem.set_color, color))
            self.play(*anims)
            self.wait()

    def define_dom_codom(self):
        dom_codom_def = self.introduce_theorem("Let $f$ be a function $X \\to Y$. \\\\ The set $X$ is the \\emph{domain} of $f$, and $Y$ is the \\emph{codomain} of $f$.", theorem_type="Definition")

        set_x = Set(name="X", color=GREEN)
        set_y = Set(name="Y", color=LAVENDER_ISH)

        self.play(*set_x.conjure(lambda s: s.move_to(1.5*LEFT), element_num=20), *set_y.conjure(lambda s: s.move_to(1.5*RIGHT), element_num=6))
        self.play(*set_x.reposition_elements(), *set_y.reposition_elements())
        self.wait()

        func = self.arbitrary_function(set_x, set_y)
        self.wait()

        dom_t = TextMobject("dom$(f) = $", "$X$")
        dom_t[1].set_color(GREEN)
        dom_t.next_to(set_x, DOWN)
        dom_t.shift(DOWN + LEFT)
        self.play(Write(dom_t))
        self.wait()

        codom_t = TextMobject("codom$(f) = $", "$Y$")
        codom_t[1].set_color(LAVENDER_ISH)
        codom_t.next_to(set_y, DOWN)
        codom_t.shift(DOWN + RIGHT)
        self.play(Write(codom_t))
        self.wait()

        self.play(FadeOutAndShift(dom_codom_def, UP),
                  FadeOutAndShift(dom_t, LEFT), FadeOutAndShift(codom_t, RIGHT),
                  FadeOut(set_x.to_fade()), FadeOut(set_y.to_fade()),
                  FadeOut(func.to_fade()))
        self.wait()

    def prove_set_of_functions_exists(self):
        func_set_def = self.introduce_theorem("$Y^X$ is the set of functions from $X$ to $Y$.", theorem_type="Definition")
        func_set_formal_def = TextMobject("$$Y^X := \\{ f \\in \\mathcal{P}(X \\times Y) : f \\text{ is a function} \\}$$")
        func_set_formal_def.next_to(func_set_def, DOWN)
        self.play(Write(func_set_formal_def))
        self.wait()

        self.refine_text(func_set_formal_def, "$$Y^X := \\{ f \\in \\mathcal{P}(X \\times Y) : \\forall x \\in X. \\exists! y \\in Y. (x,y) \\in f \\}$$", theorem_type=None, position=None)
        self.wait()

        self.refine_text(func_set_formal_def, "$$Y^X := \\{ f \\in \\mathcal{P}(X \\times Y) : f \\text{ is a function} \\}$$", theorem_type=None, position=None)
        self.wait()

        self.play(FadeOutAndShift(func_set_def, UP), FadeOutAndShift(func_set_formal_def, LEFT))
        self.wait()

        set_x = Set(name="X", color=GREEN)
        set_y = Set(name="Y", color=WHITE)

        self.play(*set_x.conjure(lambda s: s.move_to(1.5*LEFT).scale(0.16), element_num=2), *set_y.conjure(lambda s: s.move_to(1.5*RIGHT).scale(0.16), element_num=4))
        self.play(*set_x.reposition_elements(), *set_y.reposition_elements())
        self.wait()

        self.play(ApplyMethod(set_x.shift, 4.5*LEFT), ApplyMethod(set_y.shift, 4.5*RIGHT))
        self.wait()

        arrows = []
        all_sets = []

        output_tuples = list(it.product(*[set_y.get_elements() for i in set_x.get_elements()]))
        for i, output in enumerate(output_tuples):
            new_set_x = self.copy_set(set_x)
            new_set_y = self.copy_set(set_y)

            r = 2.7
            theta = i * 2*PI / len(output_tuples)

            pos = r * np.array([math.cos(theta), math.sin(theta), 0])

            self.play(ApplyMethod(new_set_x.move_to, pos + 0.3*LEFT),
                      ApplyMethod(new_set_y.move_to, pos + 0.3*RIGHT),
                      *new_set_x.change_name(None),
                      *new_set_y.change_name(None))

            func = Function(new_set_x, new_set_y, lambda x: new_set_y[output[new_set_x.get_elements().index(x)].uuid]).visualize_function(self)
            arrows.extend(func.to_fade())
            all_sets.append(new_set_x)
            all_sets.append(new_set_y)
        self.wait()

        func_set = self.pair(all_sets, name="Y^X")
        self.wait()

        self.play(FadeOut(func_set.to_fade()), FadeOut(set_x.to_fade()), FadeOut(set_y.to_fade()),
                  *[FadeOut(arr) for arr in arrows])
        self.wait()

    def function_examples(self):
        id_function_example = self.introduce_theorem("The \\emph{identity function on $X$}, $\\mathbf{1}_X : X \\to X$, is \\\\ defined by $x \\mapsto x$", theorem_type="Example")
        self.wait()

        set_x = Set(name="X")
        set_y = Set(name="X")

        self.play(*set_x.conjure(lambda s: s.move_to(1.5*LEFT), element_colors=[RED,GREEN,BLUE,PURPLE]), *set_y.conjure(lambda s: s.move_to(1.5*RIGHT), element_colors=[RED,GREEN,BLUE,PURPLE]))
        self.play(*set_x.reposition_elements(), *set_y.reposition_elements())
        self.wait()

        self.play(ApplyMethod(set_x.shift, 4.5*LEFT), ApplyMethod(set_y.shift, 4.5*RIGHT))
        set_x.scale_elements_only(1/0.3)
        set_y.scale_elements_only(1/0.3)
        self.play(ApplyMethod(set_x.scale, 0.3), ApplyMethod(set_y.scale, 0.3))
        self.play(*set_x.reposition_elements(), *set_y.reposition_elements())
        self.wait()

        prod = self.build_cartesian_product([set_x, set_y], name="X \\times X", slow_anim=False, width=5, height=3.8)
        self.wait()

        self.comprehension(prod, lambda pair: pair.get_item(0).color == pair.get_item(1).color, new_name="\\mathbf{1}_X", animate_choices=False)
        self.wait()

        self.play(FadeOut(prod.to_fade()))
        self.wait()

        set_x.ready_elements()
        set_y.ready_elements()

        self.play(ApplyMethod(set_x.shift, 4.5*RIGHT), ApplyMethod(set_y.shift, 4.5*LEFT))
        set_x.scale_elements_only(0.3)
        set_y.scale_elements_only(0.3)
        self.play(ApplyMethod(set_x.scale, 1/0.3), ApplyMethod(set_y.scale, 1/0.3))
        set_x.update_radii()
        set_y.update_radii()
        self.wait()

        func = Function(set_x, set_y, lambda x: [elem for elem in set_y.get_elements() if elem.color == x.color][0]).visualize_function(self, slow_anim=True)
        self.wait()

        self.play(FadeOutAndShift(id_function_example, UP),
                  FadeOut(set_x.to_fade()), FadeOut(set_y.to_fade()),
                  FadeOut(func.to_fade()))
        self.wait()

        constant_func_def = self.introduce_theorem("A \\emph{constant function} is a function mapping every \\\\ element to the same output.", theorem_type="Definition")
        self.wait()

        self.play(FadeOutAndShift(constant_func_def, UP))
        self.wait()

        constant_func_ex = self.introduce_theorem("Let $x_0 \\in X$, and let $f : X \\to X$ be the constant \\\\ function given by $x \\mapsto x_0$", theorem_type="Example")
        self.wait()

        set_x = Set(name="X")
        set_y = Set(name="X")

        self.play(*set_x.conjure(lambda s: s.move_to(1.5*LEFT), element_colors=[WHITE,WHITE,WHITE,WHITE,WHITE,WHITE,GREEN]),
                  *set_y.conjure(lambda s: s.move_to(1.5*RIGHT), element_colors=[WHITE,WHITE,WHITE,WHITE,WHITE,WHITE,GREEN]))
        self.play(*set_x.reposition_elements(), *set_y.reposition_elements())
        self.wait()

        func = Function(set_x, set_y, lambda x: [elem for elem in set_y.get_elements() if elem.color == GREEN][0]).visualize_function(self, slow_anim=True)
        self.wait()

        self.play(FadeOutAndShift(constant_func_ex, UP), FadeOut(set_x.to_fade()), FadeOut(set_y.to_fade()),
                  FadeOut(func.to_fade()))
        self.wait()

    def arbitrary_function(self, dom, codom, is_one_to_one=False, is_onto=False):
        func = {}
        # Copy so we don't accidentally modify codom's elements.
        available = list(codom.get_elements())

        for x in dom.get_elements():
            # NOTE: We also take this path when the function is bijective
            if is_one_to_one:
                if len(available) == 0:
                    raise Exception('Cannot build one-to-one function from {} to {}: not enough elements in the codomain'.format(dom.get_elements(), codom.get_elements()))

                y = random.choice(available)
                available.remove(y)
            elif is_onto:
                if len(available) == 0:
                    y = random.choice(codom.get_elements())
                else:
                    y = random.choice(available)
                    available.remove(y)
            else:
                y = random.choice(codom.get_elements())

            func[x.uuid] = y.uuid

        if is_onto and len(available) > 0:
            raise Exception('Cannot build onto function from {} to {}: not enough elements in the domain'.format(dom.get_elements(), codom.get_elements()))

        return Function(dom, codom, func).visualize_function(self)

    def define_functions(self):
        func_def = self.introduce_theorem("A relation $f$ between $X$ and $Y$ is called \\\\ a \\emph{function}, written $f : X \\to Y$, when every \\\\ $x \\in X$ is related (by $f$) to exactly one $y \\in Y$.", theorem_type="Definition")
        self.wait()
        clarification_text = TextMobject("That is, $f$ is a function from $X$ to $Y$ if")
        clarification_def = TextMobject("$$\\forall x \\in X. \\exists y \\in Y. (x,y) \\in f \\land \\forall z \\in Y. (x,z) \\in f \\Rightarrow y = z$$")
        clarification_def.next_to(clarification_text, DOWN)
        self.play(Write(clarification_text), Write(clarification_def))
        self.wait()
        self.refine_text(clarification_def, "$$\\forall x \\in X. \\exists y \\in Y. f(x) = y \\land \\forall z \\in Y. f(x) = z \\Rightarrow y = z$$", theorem_type=None, position=None)
        self.wait()
        self.refine_text(clarification_def, "$$\\forall x \\in X. \\exists! y \\in Y. f(x) = y$$", theorem_type=None, position=None)
        self.wait()

        self.play(FadeOutAndShift(clarification_text, LEFT), FadeOutAndShift(clarification_def, RIGHT))
        self.wait()

        self.refine_text(func_def, "$f$ is a function from $X$ to $Y$ when $\\forall x \\in X. \\exists! y \\in Y. f(x) = y$", theorem_type=None)
        self.wait()

        set_x = Set(name="X")
        set_y = Set(name="Y")

        self.play(*set_x.conjure(lambda s: s.move_to(1.5*LEFT), element_colors=[RED,GREEN,BLUE]), *set_y.conjure(lambda s: s.move_to(1.5*RIGHT), element_colors=[YELLOW,PURPLE,WHITE,ORANGE]))
        self.play(*set_x.reposition_elements(), *set_y.reposition_elements())
        self.wait()

        self.play(ApplyMethod(set_x.shift, 4.5*LEFT), ApplyMethod(set_y.shift, 4.5*RIGHT))
        set_x.scale_elements_only(1/0.3)
        set_y.scale_elements_only(1/0.3)
        self.play(ApplyMethod(set_x.scale, 0.3), ApplyMethod(set_y.scale, 0.3))
        self.play(*set_x.reposition_elements(), *set_y.reposition_elements())
        self.wait()

        prod = self.build_cartesian_product([set_x, set_y], name="X \\times Y", slow_anim=False)
        self.wait()

        func = []
        func_elems = {}
        for elem_x in set_x.get_elements():
            elem_y = random.choice(set_y.get_elements())
            func.append((elem_x.color, elem_y.color))
            func_elems[(elem_x.color, elem_y.color)] = (elem_x, elem_y)

        self.comprehension(prod, lambda pair: (pair.get_item(0).color, pair.get_item(1).color) in func, animate_choices=False, new_name='f')
        self.wait()

        for item in prod.get_elements():
            item.scale_elements_only(1/0.3)
            item.scale(1/0.8)
            item.scale_elements_only(0.8)

        self.play(ApplyMethod(prod.scale, 0.3))
        self.wait()

        texts = []
        for pair in func:
            elem_x, elem_y = func_elems[pair]

            if len(texts) == 0:
                texts.append(self.write_text_with_element(lambda s: s.to_corner(DOWN + LEFT).shift(0.5*UP), "$f($", elem_x, ") = ", elem_y, positioning=0.3*RIGHT))
            else:
                texts.append(self.write_text_with_element(lambda s: s.next_to(texts[-1], RIGHT).shift(2*RIGHT), "$f($", elem_x, ") = ", elem_y, positioning=0.3*RIGHT))

        self.wait()

        self.play(FadeOutAndShift(func_def, UP), FadeOut(prod.to_fade()),
                  FadeOut(set_x.to_fade()), FadeOut(set_y.to_fade()),
                  *[FadeOut(text) for text in texts])
        self.wait()

    def define_subsets(self):
        subset_def = self.introduce_theorem("$$X \\subseteq Y :\\Leftrightarrow \\forall z. z \\in X \\Rightarrow z \\in Y$$", theorem_type="Definition")
        self.wait()
        self.refine_text(subset_def, "A set $X$ is a subset of $Y$, written $X \\subseteq Y$, \\\\ if every element of $X$ is an element of $Y$, that is, $$\\forall z. z \\in X \\Rightarrow z \\in Y$$", theorem_type="Definition")
        self.wait()
        self.refine_text(subset_def, "$X$ is a subset of $Y$ if and only if $\\forall z. z \\in X \\Rightarrow z \\in Y$")
        self.wait()

        set_x = Set(name="X")
        set_y = Set(name="Y")

        self.play(*(set_x.conjure(lambda s: s.move_to(1.5*LEFT), element_colors=[RED,GREEN,BLUE]) +
                    set_y.conjure(lambda s: s.move_to(1.5*RIGHT), element_colors=[RED,GREEN,BLUE,YELLOW,PURPLE,ORANGE])))
        self.play(*(set_x.reposition_elements() + set_y.reposition_elements()))
        self.wait()

        self.play(ApplyMethod(set_x.shift, 4.5*LEFT), ApplyMethod(set_y.shift, 4.5*RIGHT))
        self.wait()

        set_x_2 = Set(name="X")
        self.play(*set_x_2.conjure(lambda s: s.move_to(5.5*RIGHT).scale(0.5), element_colors=[]))
        self.wait()

        groups = []

        for elem_x in set_x.get_elements():
            for elem_y in set_y.get_elements():
                if elem_x.color == elem_y.color:
                    new_elem_x = copy.deepcopy(elem_x)
                    new_elem_y = copy.deepcopy(elem_y)

                    new_elem_x.ready(False)
                    new_elem_y.ready(False)

                    self.add(new_elem_x, new_elem_y)
                    contain_x = TextMobject("$\\in X$")
                    contain_x.move_to(LEFT)
                    implies_tex = TextMobject("$\\Rightarrow$")
                    contain_y = TextMobject("$\\in Y$")
                    contain_y.move_to(RIGHT)

                    self.play(Write(contain_x), Write(implies_tex), Write(contain_y),
                              ApplyMethod(new_elem_x.next_to, contain_x, LEFT), ApplyMethod(new_elem_y.next_to, contain_y, LEFT))

                    groups.append(VGroup(new_elem_x, contain_x, implies_tex, new_elem_y, contain_y))
                    self.play(*[ApplyMethod(group.shift, 0.5*UP) for group in groups])

                    break

        implies = TexMobject("\\Rightarrow")

        subset = TexMobject("X \\subseteq Y")
        subset.move_to(0.5*DOWN)
        self.play(Write(implies), Write(subset))
        self.wait()

        self.play(FadeOutAndShift(subset_def, UP), FadeOutAndShift(implies, DOWN), FadeOutAndShift(subset, DOWN),
                  FadeOut(set_x.to_fade()), FadeOut(set_y.to_fade()), *[FadeOut(group) for group in groups])
        self.wait()

        alt_subset_def = self.introduce_theorem("A set $X$ is a subset of $Y$, written $X \\subseteq Y$, \\\\ if $X \\cup Y = Y$.", theorem_type="Definition")
        self.wait()

        set_x = Set(name="X")
        set_y = Set(name="Y")

        self.play(*set_x.conjure(lambda s: s.move_to(1.5*LEFT), element_colors=[RED,GREEN,BLUE]),
                  *set_y.conjure(lambda s: s.move_to(1.5*RIGHT), element_colors=[RED,GREEN,BLUE,YELLOW,PURPLE,ORANGE]))
        self.play(*set_x.reposition_elements(), *set_y.reposition_elements())
        self.wait()

        unioned = self.union([set_x, set_y], height_padding=1, name='X \\cup Y')
        self.wait()

        self.play(ApplyMethod(unioned.shift, 2*LEFT))
        unioned.scale_elements_only(1/0.5)
        self.play(ApplyMethod(unioned.scale, 0.5))
        self.play(*unioned.reposition_elements())
        self.wait()

        set_y = Set(name="Y")
        self.play(*set_y.conjure(lambda s: s.move_to(1.5*RIGHT), element_colors=[RED,GREEN,BLUE,YELLOW,PURPLE,ORANGE]))
        self.play(*set_y.reposition_elements())
        self.wait()

        to_remove_colors = [RED,GREEN,BLUE]
        anims = []
        for elem in unioned.get_elements():
            if elem.color in to_remove_colors:
                unioned.remove_element(elem)
                anims.append(FadeOut(elem))
                to_remove_colors.remove(elem.color)
        self.play(*anims)
        self.wait()

        equality = TexMobject("=")
        self.play(Write(equality),
                  ApplyMethod(unioned.next_to, equality, 2*LEFT),
                  ApplyMethod(set_y.next_to, equality, RIGHT))
        self.wait()

        self.play(FadeOutAndShift(alt_subset_def, UP), FadeOutAndShift(equality, DOWN),
                  FadeOut(unioned.to_fade()), FadeOut(set_y.to_fade()))
        self.wait()

        equiv_prop = self.introduce_theorem("The previous definitions are equivalent; \\\\$\\forall z. z \\in X \\Rightarrow z \\in Y$ if and only if $X \\cup Y = Y$", theorem_type="Proposition")
        self.wait()

        forward = TextMobject("($\\Rightarrow$): Suppose $\\forall z. z \\in X \\Rightarrow z \\in Y$.")
        forward = TextMobject("($\\Rightarrow$): Suppose $\\forall z.$", "$z \\in X$", "$\\Rightarrow$", "$z \\in Y$.")
        forward.next_to(equiv_prop, DOWN)
        forward.shift(2.8*LEFT)
        self.play(Write(forward))
        self.wait()

        set_x = Set(name="X")
        set_y = Set(name="Y")

        self.play(*set_x.conjure(lambda s: s.move_to(1.5*LEFT), element_colors=[RED,RED,RED,RED,RED]),
                  *set_y.conjure(lambda s: s.move_to(1.5*RIGHT), element_colors=[BLUE,BLUE,BLUE,RED,RED,RED,RED,RED]))
        self.play(*set_x.reposition_elements(), *set_y.reposition_elements())
        self.wait()

        self.play(ApplyMethod(set_x.shift, 4.5*LEFT), ApplyMethod(set_y.shift, 4.5*RIGHT))
        set_x.scale_elements_only(1/0.3)
        set_y.scale_elements_only(1/0.3)
        self.play(ApplyMethod(set_x.scale, 0.3), ApplyMethod(set_y.scale, 0.3))
        self.play(*set_x.reposition_elements(), *set_y.reposition_elements())
        self.wait()

        set_x_copy = self.copy_set(set_x)
        set_y_copy = self.copy_set(set_y)

        self.play(ApplyMethod(set_x_copy.shift, 5.5*RIGHT), ApplyMethod(set_y_copy.shift, 5.5*LEFT))
        self.wait()

        unioned = self.pair([set_x_copy, set_y_copy], name='X \\cup Y', height_padding=2)
        # NOTE: Unclear why, it seems we need to re-add these elements...
        for elem in set_x_copy.get_elements() + set_y_copy.get_elements():
            self.add(elem)
        self.wait()
        self.union_col(unioned)
        self.wait()

        to_remove_colors = [RED,RED,RED,RED,RED]
        anims = []
        for elem in unioned.get_elements():
            if elem.color in to_remove_colors:
                unioned.remove_element(elem)
                anims.append(FadeOut(elem))
                to_remove_colors.remove(elem.color)
        self.play(*anims)
        self.wait()

        take_elem_text = TextMobject("Take an element from $X \\cup Y$:")
        take_elem_text.to_corner(DOWN + LEFT)
        self.play(Write(take_elem_text))
        self.wait()

        x_dummy_elem = set_x.get_elements()[0]
        if_in_x_text = self.write_text_with_element(lambda it: it.next_to(take_elem_text, 0.25*UP + RIGHT), "if", x_dummy_elem, "$\\in X$\\relax")
        self.wait()

        forward_highlighted = TextMobject("($\\Rightarrow$): Suppose $\\forall z.$", "$\\mathbf{z \\in X}$", "$\\Rightarrow$", "$\\mathbf{z \\in Y}$.")
        forward_highlighted[1].set_color(RED)
        forward_highlighted[3].set_color(BLUE)
        forward_highlighted.move_to(forward)
        self.play(Transform(forward, forward_highlighted))
        self.wait()

        then_x_text = self.write_text_with_element(lambda it: it.next_to(if_in_x_text, RIGHT), ", then", x_dummy_elem, "$\\in Y$")
        self.wait()

        forward_original = TextMobject("($\\Rightarrow$): Suppose $\\forall z.$", "$z \\in X$", "$\\Rightarrow$", "$z \\in Y$.")
        forward_original.move_to(forward)
        self.play(Transform(forward, forward_original))
        self.wait()

        # Pick some arbitrary non-red element from Y to display
        y_dummy_elem = [elem for elem in set_y.get_elements() if elem.color != RED][0]
        if_in_y_text = self.write_text_with_element(lambda it: it.next_to(take_elem_text, RIGHT), "if", y_dummy_elem, "$\\in Y$")
        self.wait()
        then_y_text = self.write_text_with_element(lambda it: it.next_to(if_in_y_text, RIGHT), ", then", y_dummy_elem, "$\\in Y$")
        self.wait()

        cases_group = VGroup(if_in_x_text, if_in_y_text, then_y_text, then_x_text)

        then_done = TextMobject("it is in $Y$, so $X \\cup Y = Y$.")
        then_done.next_to(take_elem_text, RIGHT)
        self.play(Transform(cases_group, then_done))
        self.wait()

        self.play(FadeOutAndShift(forward, LEFT),
                  FadeOutAndShift(take_elem_text, DOWN),
                  FadeOutAndShift(cases_group, DOWN),
                  FadeOut(set_x.to_fade()), FadeOut(set_y.to_fade()), FadeOut(unioned.to_fade()))
        self.wait()

        backward = TextMobject("($\\Leftarrow$): Suppose $X \\cup Y = Y$.")
        backward.next_to(equiv_prop, DOWN)
        backward.shift(2.8*LEFT)
        self.play(Write(backward))
        self.wait()

        set_x = Set(name="X")
        set_y = Set(name="Y")

        self.play(*set_x.conjure(lambda s: s.move_to(1.5*LEFT), element_colors=[RED,GREEN,BLUE]),
                  *set_y.conjure(lambda s: s.move_to(1.5*RIGHT), element_colors=[RED,GREEN,BLUE,YELLOW,PURPLE,ORANGE]))
        self.play(*set_x.reposition_elements(), *set_y.reposition_elements())
        self.wait()

        unioned = self.union([set_x, set_y], height_padding=1, name='X \\cup Y')
        self.wait()

        to_remove_colors = [RED,GREEN,BLUE]
        anims = []
        for elem in unioned.get_elements():
            if elem.color in to_remove_colors:
                unioned.remove_element(elem)
                anims.append(FadeOut(elem))
                to_remove_colors.remove(elem.color)
        self.play(*anims)
        self.wait()

        take_elem_x = TextMobject("Take an element from $X$.")
        take_elem_x.to_corner(DOWN+LEFT)
        self.play(Write(take_elem_x))
        self.wait()

        x_dummy_elem = [elem for elem in unioned.get_elements() if elem.color in [RED,GREEN,BLUE]][0]
        in_x_text = self.write_text_with_element(lambda it: it.next_to(take_elem_x, RIGHT), "If", x_dummy_elem, "$\\in X$")
        self.wait()

        then_in_union = self.write_text_with_element(lambda it: it.next_to(in_x_text, RIGHT), ", then", x_dummy_elem, "$\\in X \\cup Y$")
        self.wait()

        new_then_in = TextMobject("$\\in Y$")
        new_then_in.next_to(then_in_union[-2], RIGHT)

        self.play(Transform(then_in_union[-1], new_then_in))
        self.wait()

        self.play(FadeOutAndShift(backward, LEFT), FadeOutAndShift(take_elem_x, DOWN),
                  FadeOutAndShift(in_x_text, DOWN), FadeOutAndShift(then_in_union, DOWN),
                  FadeOut(unioned.to_fade()))
        self.wait()

        qed = TextMobject("\\large $\\square$")
        qed.move_to(equiv_prop.get_corner(DOWN + RIGHT))
        qed.shift(DOWN)
        self.play(Write(qed))
        self.wait()

        self.play(FadeOutAndShift(equiv_prop, UP), FadeOutAndShift(qed, RIGHT))
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

    def copy_set(self, to_copy):
        new_set = copy.deepcopy(to_copy)
        if new_set.name_obj is not None:
            new_set.name_obj.clear_updaters()
            new_set.name_obj.add_updater(lambda nm: nm.next_to(new_set.shape, DOWN))
            self.add(new_set.name_obj)

        old_elems = new_set.clear_elements()
        for elem in old_elems:
            new_set.take_elements([elem])
            self.add(elem)

        return new_set

    def define_relation(self):
        rel_def = self.introduce_theorem("A relation $R$ between sets $X$ and $Y$ is a subset \\\\ of the product $X \\times Y$.", theorem_type="Definition")
        self.refine_text(rel_def, "A relation $R$ between sets $X$ and $Y$ is a subset of $X \\times Y$.", theorem_type=None)

        set_a = Set(name="X")
        set_b = Set(name="Y")

        self.play(*set_a.conjure(lambda s: s.move_to(1.5*LEFT), element_colors=[RED,GREEN,BLUE]))
        self.play(*set_b.conjure(lambda s: s.move_to(1.5*RIGHT), element_colors=[PURPLE,YELLOW,ORANGE]))
        self.play(*set_a.reposition_elements())
        self.play(*set_b.reposition_elements())
        self.wait()

        self.play(ApplyMethod(set_a.shift, 4.5*LEFT), ApplyMethod(set_b.shift, 4.5*RIGHT))
        set_a.scale_elements_only(1/0.3)
        set_b.scale_elements_only(1/0.3)
        self.play(ApplyMethod(set_a.scale, 0.3), ApplyMethod(set_b.scale, 0.3))
        self.play(*set_a.reposition_elements(), *set_b.reposition_elements())
        self.wait()

        prod = self.build_cartesian_product([set_a, set_b], name="X \\times Y", slow_anim=True)
        self.wait()

        self.play(FadeOutAndShift(rel_def), FadeOut(prod.to_fade()),
                  FadeOut(set_a.to_fade()), FadeOut(set_b.to_fade()))
        self.wait()

    def relation_example_equality(self):
        rel_ex = self.introduce_theorem("Let $R$ be $\\{ (x,y) \\in X \\times X : x = y \\}$.", theorem_type="Example")

        set_a = Set(name="X")
        set_b = Set(name="X")

        self.play(*set_a.conjure(lambda s: s.move_to(1.5*LEFT), element_colors=[RED,GREEN,BLUE,PURPLE]))
        self.play(*set_b.conjure(lambda s: s.move_to(1.5*RIGHT), element_colors=[RED,GREEN,BLUE,PURPLE]))
        self.play(*set_a.reposition_elements())
        self.play(*set_b.reposition_elements())
        self.wait()

        self.play(ApplyMethod(set_a.shift, 4.5*LEFT), ApplyMethod(set_b.shift, 4.5*RIGHT))
        set_a.scale_elements_only(1/0.3)
        set_b.scale_elements_only(1/0.3)
        self.play(ApplyMethod(set_a.scale, 0.3), ApplyMethod(set_b.scale, 0.3))
        self.play(*set_a.reposition_elements(), *set_b.reposition_elements())
        self.wait()

        prod = self.build_cartesian_product([set_a, set_b], name="X \\times X", slow_anim=True)
        self.wait()

        self.comprehension(prod, lambda pair: pair.get_item(0).color == pair.get_item(1).color, new_name="R")
        self.wait()

        self.play(FadeOutAndShift(rel_ex, UP), FadeOut(prod.to_fade()),
                  FadeOut(set_a.to_fade()), FadeOut(set_b.to_fade()))
        self.wait()

    def build_cartesian_product(self, sets, name=None, slow_anim=False, width=7, height=6):
        tuples = []
        # TODO: Add a slow_anim version that builds them and sends the elements flying into the ordered pairs
        for items in it.product(*[s.get_elements() for s in sets]):
            pair = OrderedPair(items)
            tuples.append(pair)

        prod = self.pair(tuples, name=name, height_padding=height, width_padding=width)
        scaling = PI*np.mean([prod.get_width(), prod.get_height()]) / (1.8 * tuples[0].get_width() * len(tuples))
        for pair in tuples:
            pair.scale_elements_only(1/scaling)
            pair.scale(scaling)
        prod.do_reposition_elements(evenly=0.8)

        anims = []
        for pair in tuples:
            if slow_anim:
                self.play(*pair.create())
            else:
                anims.extend(pair.create())

        if not slow_anim:
            self.play(*anims)

        return prod

    def define_ordered_pairs(self):
        pair_def = self.introduce_theorem("$(x,y) := \\{\\{x\\}, \\{x,y\\}\\}$", theorem_type="Definition")

        set_a = Set(color=RED)
        set_b = Set(color=BLUE)

        self.play(*set_a.conjure(lambda s: s.move_to(RIGHT), element_num=60))
        self.play(*set_b.conjure(lambda s: s.move_to(3.5*RIGHT), element_num=3))
        self.play(*set_a.reposition_elements())
        self.play(*set_b.reposition_elements())

        pair_right = self.pair([set_a, set_b], name='\\{A,B\\}')
        self.wait()

        set_a_cpy = Set(color=RED)
        self.play(*set_a_cpy.conjure(lambda s: s.move_to(3.5*LEFT), element_num=60))
        self.play(*set_a_cpy.reposition_elements())
        self.wait()

        pair_left = self.pair([set_a_cpy], name='\\{A\\}', width_padding=0)
        self.wait()

        ordered_pair = self.pair([pair_left, pair_right], name='(A,B)', height_padding=2.75)
        self.wait()

        self.play(FadeOutAndShift(pair_def, UP), FadeOut(ordered_pair.to_fade()))
        self.wait()

    def define_cartesian_product(self):
        cart_prod_def = self.introduce_theorem("$$X \\times Y := \\{(x,y) : x \\in X \\land y \\in Y\\}$$", theorem_type="Definition")
        self.refine_text(cart_prod_def, "$$X \\times Y := $$ $$\\{(x,y) : x \\in X, y \\in Y\\}$$", theorem_type="Definition")
        self.refine_text(cart_prod_def, "$$X \\times Y := $$ $$\\{(x,y) : x \\in X, y \\in Y\\}$$???", theorem_type="Definition")
        self.wait()
        self.refine_text(cart_prod_def, "$$X \\times Y := $$ $$\\{z \\in \\mathcal{P}(\\mathcal{P}(X \\cup Y)) : \\exists x. x \\in X \\land \\exists y. y \\in Y \\land z = (x, y)\\}$$", theorem_type="Definition")
        self.refine_text(cart_prod_def, "$$X \\times Y := $$ $$\\{z \\in \\mathcal{P}(\\mathcal{P}(X \\cup Y)) : \\exists x. x \\in X \\land \\exists y. y \\in Y \\land z = \\{\\{x\\}, \\{x,y\\}\\}\\}$$", theorem_type="Definition")
        self.refine_text(cart_prod_def, "$$X \\times Y := $$ $$\\{z \\in \\mathcal{P}(\\mathcal{P}(X \\cup Y)) : \\exists x. x \\in X \\land \\exists y. y \\in Y \\land z = (x,y)\\}$$", theorem_type="Definition")
        self.wait()
        self.refine_text(cart_prod_def, "$$X \\times Y := \\{z \\in \\mathcal{P}(\\mathcal{P}(X \\cup Y)) : \\exists x \\in X. \\exists y \\in Y. z = (x,y)\\}$$", theorem_type="Definition")
        self.refine_text(cart_prod_def, "$$X \\times Y := \\{z \\in \\mathcal{P}(\\mathcal{P}(X \\cup Y)) : \\exists x \\in X, y \\in Y. z = (x,y)\\}$$", theorem_type="Definition")
        self.wait()
        self.play(FadeOutAndShift(cart_prod_def, UP))
        self.wait()

        set_a = Set()
        set_b = Set()

        self.play(*set_a.conjure(lambda s: s.move_to(0.1*LEFT).scale(0.25), element_colors=[RED]))
        self.play(*set_b.conjure(lambda s: s.move_to(0.1*RIGHT).scale(0.25), element_colors=[GREEN, BLUE]))
        self.play(*(set_a.reposition_elements() + set_b.reposition_elements()))

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
        self.play(*pset2.reposition_elements())
        self.wait()

        cart_prod_def = self.write_theorem("$$X \\times Y := \\{z \\in \\mathcal{P}(\\mathcal{P}(X \\cup Y)) : \\exists x \\in X, y \\in Y. z = (x,y)\\}$$", theorem_type=None)
        self.wait()

        self.play(FadeOutAndShift(cart_prod_def, UP), FadeOut(pset2.to_fade()))
        self.wait()

    def prove_singleton_exists(self):
        singletons = self.introduce_theorem("For any set $A$, the singleton $\\{A\\}$ is a set.")
        set_a = Set(color=RED)
        set_a_cpy = Set(color=RED)

        self.play(*set_a.conjure(lambda s: s.move_to(1.5*LEFT), element_num=45))
        self.play(*set_a.reposition_elements())
        self.play(*set_a_cpy.conjure(lambda s: s.move_to(1.5*RIGHT), element_num=45))
        self.play(*set_a_cpy.reposition_elements())

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

        self.play(FadeOut(set_a_cpy.to_fade()))
        self.wait()

        self.play(FadeOutAndShift(singletons, UP), FadeOut(paired.to_fade()))
        self.wait()

    def prove_union_two_sets(self):
        union_two = self.introduce_theorem("The union of any two sets $A$ and $B$, $A \\cup B$, \\\\ is a set.")
        set_a = Set(color=RED)
        set_b = Set(color=BLUE)

        self.play(*set_a.conjure(lambda s: s.move_to(1.5*LEFT), element_num=45))
        self.play(*set_a.reposition_elements())
        self.play(*set_b.conjure(lambda s: s.move_to(1.5*RIGHT), element_num=80))
        self.play(*set_b.reposition_elements())

        unioned = self.pair([set_a, set_b], name='\\{A, B\\}', height_padding=1.5)
        self.union_col(unioned, new_name='A \\cup B')
        self.wait()

        self.play(FadeOutAndShift(union_two, UP), FadeOut(unioned.to_fade()))
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
                  FadeOut(set_x.to_fade()))
        self.wait()

    def prove_empty_set_exists_formal(self):
        with open('formal_proof.txt') as f:
            contents = f.read()

        empty_set_exists = self.introduce_theorem("The empty set exists.")
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
        self.play(*set_x.reposition_elements())
        self.wait()

        self.comprehension(set_x, lambda elem: random.choice([True, False]), new_name='Y')
        self.wait(3)

        self.play(FadeOutAndShift(name, UP), FadeOutAndShift(axiom_compr, UP),
                  FadeOut(set_x.to_fade()))
        self.wait()

    def show_axiom_union(self):
        name, axiom_three = self.introduce_statement("Union", "$\\forall \\mathcal{C}. \\exists U. \\forall x. x \\in U \\Leftrightarrow \\exists A. A \\in \\mathcal{C} \\land x \\in A$")

        set_a = Set(color=RED)
        set_b = Set(color=BLUE)
        set_c = Set(color=GREEN)
        set_d = Set(color=PURPLE)

        self.play(*set_a.conjure(lambda s: s.move_to(1.1*UP), element_num=5))
        self.play(*set_a.reposition_elements())
        self.play(*set_b.conjure(lambda s: s.move_to(2*RIGHT), element_num=20))
        self.play(*set_b.reposition_elements())
        self.play(*set_c.conjure(lambda s: s.move_to(1.1*DOWN), element_num=60))
        self.play(*set_c.reposition_elements())
        self.play(*set_d.conjure(lambda s: s.move_to(2*LEFT), element_num=25))
        self.play(*set_d.reposition_elements())

        unioned = self.pair([set_a, set_b, set_c, set_d], name='\\mathcal{C}')
        self.union_col(unioned, new_name='U')

        self.refine_text(axiom_three, "$\\forall \\mathcal{C}. \\exists U. U = \\bigcup \\mathcal{C}$", position=UP+RIGHT)

        self.play(FadeOutAndShift(name, UP), FadeOutAndShift(axiom_three, UP),
                  FadeOut(unioned.to_fade()))
        self.wait()

    def show_axiom_powerset(self):
        name, axiom_four = self.introduce_statement("Powerset", "$\\forall X. \\exists P. \\forall A. A \\in P \\Leftrightarrow (\\forall y. y \\in A \\Rightarrow Y \\in X)$")

        set_x = Set(shape=Circle(radius=0.8, color=WHITE), color=WHITE, name='X')
        self.play(*set_x.conjure(element_colors=[RED,GREEN,BLUE,PURPLE]))
        self.play(*set_x.reposition_elements())
        self.wait()

        new_sets = self.powerset(set_x, slow_anim=True)

        pset_set = self.pair(new_sets, name="P")

        self.refine_text(axiom_four, "$\\forall X. \\exists P. \\forall A. A \\in P \\Leftrightarrow A \\subseteq X$", position=UP+RIGHT)
        self.refine_text(axiom_four, "$\\forall X. \\exists P. P = \\mathcal{P}(X)$", position=UP+RIGHT)

        self.play(FadeOutAndShift(axiom_four, UP), FadeOutAndShift(name, UP), FadeOut(pset_set.to_fade()))
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
                  FadeOut(ax0_set.to_fade()))
        self.wait()

    def show_axiom_extensionality(self):
        name, axiom_one = self.introduce_statement("Extensionality", "$\\forall X. \\forall Y. \\forall z. (z \\in X \\Leftrightarrow z \\in Y) \\Rightarrow X = Y$")

        colors = ['#D999FF', '#AC8BE8', '#ADA6FF', '#8B9CE8', '#99C6FF']
        set_x = Set(name="X")
        set_y = Set(name="Y")
        self.play(*(set_x.conjure(lambda s: s.move_to(3*LEFT), element_colors=colors) +
                    set_y.conjure(lambda s: s.move_to(3*RIGHT), element_colors=colors)))
        self.play(*set_x.reposition_elements())
        self.play(*set_y.reposition_elements())

        to_fade = []
        gs = []

        for ex, ey in zip(set_x.get_elements(), set_y.get_elements()):
            new_ex = copy.copy(ex)
            new_ey = copy.copy(ey)
            new_ex.clear_updaters()
            new_ey.clear_updaters()

            self.add(new_ex)
            self.add(new_ey)

            contain_x = TextMobject("$\\in X$")
            contain_x.move_to(LEFT)
            and_tex = TextMobject("$\\land$")
            contain_y = TextMobject("$\\in Y$")
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
                  FadeOut(set_x.to_fade()),
                  FadeOut(set_y.to_fade()))
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
        self.play(*(set_x.conjure(lambda s: s.move_to(1.5*LEFT), element_num=10) +
                    set_y.conjure(lambda s: s.move_to(1.5*RIGHT), element_num=50)))
        self.play(*set_x.reposition_elements())
        self.play(*set_y.reposition_elements())
        self.wait()

        paired = self.pair([set_x, set_y], name="Z")
        self.wait()

        self.refine_text(axiom_two, "$\\forall X. \\forall Y. \\exists Z. Z = \{X, Y\}$", position=UP+RIGHT)

        self.play(FadeOutAndShift(name, UP), FadeOutAndShift(axiom_two, UP),
                  FadeOut(paired.to_fade()))
        self.wait()

    def union_col(self, col, new_name=None):
        anims = []

        old_elems = col.clear_elements()
        for s in old_elems:
            # TODO: What to do with elements and pairs? Do we even need to worry about this?
            if isinstance(s, Set):
                col.take_elements(s.clear_elements())
                anims.append(FadeOut(s.to_fade()))

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
        self.play(*ax0_set.reposition_elements())
        return ax0_set

    def comprehension(self, set_x, pred, new_name=None, animate_choices=True):
        anims = []
        to_fade = []
        to_remove = []

        self.play(*set_x.reposition_elements(evenly=0.7))

        set_x.unready_elements()

        for elem in set_x.get_elements():
            varphi = TexMobject("\\varphi(")
            close_paren = TexMobject(")")

            varphi.next_to(elem, 0.1*LEFT)
            close_paren.next_to(elem, 0.1*RIGHT)

            if pred(elem):
                varphi.set_color(GREEN)
                close_paren.set_color(GREEN)
            else:
                varphi.set_color(RED)
                close_paren.set_color(RED)
                to_remove.append(elem)

            if animate_choices:
                to_fade.append(varphi)
                to_fade.append(close_paren)

                anims.append(Write(varphi))
                anims.append(Write(close_paren))

        if animate_choices:
            self.play(*anims)
            self.wait()

        for elem in to_remove:
            set_x.remove_element(elem)

        anims = [FadeOut(o) for o in to_fade]
        anims.extend([FadeOut(o.to_fade()) for o in to_remove])
        self.play(*anims)
        if new_name is not None:
            self.play(*set_x.change_name(new_name))
        self.wait()

        self.play(*set_x.reposition_elements(evenly=0.7))
        set_x.ready_elements()

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

