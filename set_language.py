#!/usr/bin/env python

from manimlib.imports import *

import itertools as it
import uuid

BORDER_FACTOR = 0.98
COLLISION_TOLERANCE = 0.99

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

class Resolvable:
    def __init__(self):
        pass

    def object(self):
        raise NotImplementedError()

    def display_object(self):
        raise NotImplementedError()

class Value(Resolvable):
    def __init__(self, obj):
        super().__init__()
        self.obj = obj

    def object(self):
        return self.obj

    def display_object(self):
        return self.obj

    def latex(self):
        raise NotImplementedError()

class IntValue(Value):
    def __init__(self, value):
        self.value = value
        super().__init__(TexMobject(self.latex()))
        self.obj.scale(0.5)

    def latex(self):
        return str(self.value)

class SetValue(Value):
    def __init__(self, elements):
        self.elements = elements
        super().__init__(TexMobject(self.latex()))
        self.obj.scale(0.5)

    def latex(self):
        return '\\left\\{' + ', '.join([e.value.latex() for e in self.elements]) + '\\right\\}'

class Element(Resolvable):
    def __init__(self, elements, value=None, data=None, obj_gen=SmallDot, moving=True, parent=None):
        super().__init__()

        self.parent = parent

        self.moving = False
        self.radii = None

        self.drawn = False
        self.home_pos = np.array([0.0,0.0,0.0])

        self.elements = elements
        if data is None:
            self.data = {}
        else:
            self.data = data
        self.value = value

        self.obj = obj_gen()

        for e in self.elements:
            e.set_parent(self.object())

        if self.value is not None:
            self.display_obj = VGroup(self.object(), self.value.object())
            self.value.object().add_updater(lambda obj, dt: obj.next_to(self.object(), UP))
        else:
            self.display_obj = self.obj

        self.set_parent(self.parent)

        self.speed = 0.9*np.mean(self.radii)
        self.dir = random.uniform(0, 2*PI)

        self.uuid = str(uuid.uuid4())

        self.move(moving)

    def update_value(self, new_value):
        anims = []
        old_value = self.value
        self.value = new_value
        if self.value is not None:
            self.display_obj = VGroup(self.object(), self.value.object())
            self.value.object().add_updater(lambda obj, dt: obj.next_to(self.object(), UP))
        if self.drawn:
            anims.append(Transform(old_value.object(), self.value.object()))
        return anims

    # TODO: This assumes circles...
    def overlaps_with(self, other):
        # Divide by 4 because average of the two and they are diameters
        r1 = (self.object().get_width() + self.object().get_height()) / 4
        r2 = (other.object().get_width() + other.object().get_height()) / 4

        diff = self.object().get_center() - other.object().get_center()

        return np.dot(diff, diff) < (r1 + r2)**2

    def overlaps_with_any(self, elements):
        return any(map(lambda e2: self.overlaps_with(e2) and self is not e2, elements))

    def scale(self, amount, recursive=True):
        self.display_object().scale(amount)
        if recursive:
            for e in self.elements:
                e.scale(amount, recursive=recursive)
        return self.update_radii()

    def scale_object(self, amount, recursive=True):
        self.object().scale(amount)
        if recursive:
            for e in self.elements:
                e.scale_object(amount, recursive=recursive)
        return self.update_radii()

    def object(self):
        return self.obj

    def display_object(self):
        return self.display_obj

    def set_parent(self, new_parent):
        self.anchor_to(new_parent)

        if not self.in_parent(self.object().get_x(), self.object().get_y()):
            return self.reposition()

    def anchor_to(self, new_parent):
        self.parent = new_parent
        self.update_radii()

        self.object().clear_updaters()
        self.object().add_updater(lambda obj, dt: self.update_position(dt))

        return self

    def update_radii(self):
        # NOTE: This will only work for circles or ellipses.
        if self.parent is not None:
            radius_x = (self.parent.get_width() - self.object().get_width()) / 2.0
            radius_y = (self.parent.get_height() - self.object().get_height()) / 2.0
            self.radii = np.array([radius_x, radius_y, 1])
        else:
            self.radii = np.array([0,0,1])

        for e in self.elements:
            e.update_radii()

        return self

    def freeze_at_home(self):
        return [ApplyMethod(self.object().move_to, self.home_pos)] + [ anim for e in self.elements for anim in e.freeze_at_home() ]

    def reposition(self, angle=None, offset_radius=0.5):
        self.home_pos = self.get_new_position(angle=angle, offset_radius=offset_radius)
        return self.move_to(self.home_pos[0], self.home_pos[1])

    def get_new_position(self, angle=None, offset_radius=0.5):
        self.update_radii()

        if self.parent is not None:
            if angle is None:
                offset_angle = random.uniform(0, 2*PI)
                offset_radius = random.uniform(0, 1) * 0.9 # Make sure we don't end up outside self.parent
            else:
                offset_angle = angle

            return np.array([offset_radius * math.cos(offset_angle) * self.radii[0] + self.parent.get_x(),
                             offset_radius * math.sin(offset_angle) * self.radii[1] + self.parent.get_y(), 0])
        else:
            return np.array([self.object().get_x(), self.object().get_y(), 0])

    def move(self, val=True):
        self.moving = val
        return self

    def draw(self):
        if self.drawn:
            return []
        else:
            self.drawn = True
            return [ShowCreation(self.display_object())] + [anim for e in self.elements for anim in e.draw()]

    def fade_value(self):
        return [FadeOut(self.value.object())]

    def fade(self, recursive=True):
        anims = []
        if self.drawn:
            self.drawn = False
            anims.append(FadeOut(self.display_object()))

        if recursive:
            anims.extend([anim for e in self.elements for anim in e.fade()])

        return anims

    def update_position(self, dt):
        if self.moving:
            for i in range(3):
                dx = dt*self.speed*math.cos(self.dir)
                dy = dt*self.speed*math.sin(self.dir)
                new_x = self.object().get_x() + dx
                new_y = self.object().get_y() + dy

                if self.in_parent(new_x, new_y) and self.in_bounds(new_x, new_y):
                    self.shift(dx, dy)
                    return self

                self.dir = random.uniform(0, 2*PI)

        return self

    def shift(self, dx, dy):
        for e in self.elements:
            e.shift(dx, dy)
        self.object().shift(np.array([dx, dy, 0]))
        return self

    def move_to(self, x, y):
        dx = x - self.object().get_x()
        dy = y - self.object().get_y()
        return self.shift(dx, dy)

    def in_bounds(self, new_x, new_y):
        w = BORDER_FACTOR*FRAME_WIDTH/2
        h = BORDER_FACTOR*FRAME_HEIGHT/2
        return new_x + self.object().get_width() / 2.0 < w and new_y + self.object().get_height() / 2.0 < h and new_x - self.object().get_width() / 2.0 > -w and new_y - self.object().get_height() / 2.0 > -h

    def in_parent(self, new_x, new_y):
        if self.radii[0] == 0 or self.radii[1] == 0:
            return True
        else:
            pt = np.array([new_x, new_y, 0])
            t = (pt - self.parent.get_center()) / self.radii
            return np.dot(t, t) < COLLISION_TOLERANCE**2

    def equality_test(self, other):
        result = True
        anims = []

        self.move(False)
        other.move(False)

        for e1 in self.elements:
            match = None
            for e2 in other.elements:
                b, new_anims = e1.equality_test(e2)
                anims.extend(new_anims)
                if b:
                    match = e2

            if match is None:
                result = False

        return result, anims

    def remove_elements(self, to_remove=None):
        removed = []
        if to_remove is None:
            removed = self.elements
        else:
            removed = to_remove

        self.elements = [e for e in self.elements if e not in removed]

        return removed

    def add_elements(self, new_elements):
        self.elements.extend(new_elements)
        for e in new_elements:
            e.set_parent(self.object())
        return self

def calculate_size(elements):
    min_x = 0
    max_x = 0
    min_y = 0
    max_y = 0

    for e in elements:
        x_low = e.object().get_x() - e.object().get_width() / 2.0
        x_high = e.object().get_x() + e.object().get_width() / 2.0

        y_low = e.object().get_y() - e.object().get_height() / 2.0
        y_high = e.object().get_y() + e.object().get_height() / 2.0

        min_x = min(x_low, min_x)
        max_x = max(x_high, max_x)

        min_y = min(y_low, min_y)
        max_y = max(y_high, max_y)

    return max_x - min_x, max_y - min_y

class Integer(Element):
    def __init__(self, value, moving=True):
        super().__init__([], value=IntValue(value), moving=moving)

class Set(Element):
    WIDTH_PADDING = 0.2
    HEIGHT_PADDING = 0.2
    WIDTH_FACTOR = 1.1
    HEIGHT_FACTOR = 1.1

    RETRY_OVERLAP = 10

    def __init__(self, elements, moving=False):
        super().__init__(elements, value=SetValue(elements), obj_gen=lambda: Ellipse(color=WHITE, width=1, height=1), moving=moving)

        self.envelope_elements()
        self.arrange_elements()

        # Try to avoid elements overlapping
        # for e1 in self.elements:
        #     for n in range(Set.RETRY_OVERLAP):
        #         if e1.overlaps_with_any(self.elements):
        #             e1.reposition()
        #         else:
        #             break

    def envelope_elements(self):
        w, h = calculate_size(self.elements)
        self.object().scale(2 * np.sqrt(w**2 + h**2))

        self.update_radii()
        return self

    def arrange_elements(self):
        for i, e in enumerate(self.elements):
            theta = i * 2 * PI / len(self.elements)

            offset_x = self.object().get_width() / 2.0 * math.cos(theta)
            offset_y = self.object().get_height() / 2.0 * math.sin(theta)
            e.move_to(offset_x, offset_y)

    def scale_sets(self, amount, recursive=True):
        self.object().scale(amount)
        if recursive:
            for e in self.elements:
                if isinstance(e, Set):
                    e.scale_sets(amount, recursive=recursive)
        return self.update_radii()

    def union(self):
        anims = []
        to_keep = []
        new_elements = []
        for e in self.elements:
            if isinstance(e, Set):
                anims.extend(e.fade(recursive=False))
                new_elements.extend(e.remove_elements())
            else:
                to_keep.append(e)
        self.elements = to_keep
        self.add_elements(new_elements)
        anims.extend(self.update_value(SetValue(self.elements)))
        return anims

class Interpreter(Scene):
    def construct(self):
        # A = { 1,2,3 }
        # a = Set([Integer(1), Integer(2), Integer(3)])
        # a.shift(4, 0)
        # self.play(*a.draw())
        # self.wait()

        # B = { 4,5,6 }
        # b = Set([Integer(4), Integer(5)])
        # b.shift(-4,0)
        # self.play(*b.draw())
        # self.wait()

        # C = { {1}, {2,-1} }
        c = Set([Set([Integer(1)]).shift(-1, 0), Set([Integer(2), Integer(-1)]).shift(1, 0)])
        c.scale_sets(2)
        self.play(*c.draw())
        self.wait(2)
        self.play(*c.union())
        # a.shift(-1,0)
        self.wait(10)

