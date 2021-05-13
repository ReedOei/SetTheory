#!/usr/bin/env python

from manimlib.imports import *

import itertools as it
import uuid

BORDER_FACTOR = 0.98

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

class IntValue(Value):
    def __init__(self, value):
        super().__init__(TextMobject(str(value)))
        self.value = value

        self.obj.scale(0.5)

class Element(Resolvable):
    def __init__(self, elements, value=None, data=None, obj_gen=SmallDot):
        super().__init__()

        self.parent = None

        self.is_ready = False
        self.radii = None

        self.drawn = False

        self.elements = elements
        if data is None:
            self.data = {}
        else:
            self.data = data
        self.value = value

        self.obj = obj_gen()

        if self.value is not None:
            self.display_obj = VGroup(self.object(), self.value.object())
            self.value.object().add_updater(lambda obj, dt: obj.next_to(self.object(), UP))
        else:
            self.display_obj = self.obj

        self.anchor_to(self.parent)
        self.object().move_to(self.reposition())

        self.speed = 0.9*np.mean(self.radii)
        self.dir = random.uniform(0, 2*PI)

        self.uuid = str(uuid.uuid4())
        self.collision_tolerance = 0.99

        self.ready()

    def object(self):
        return self.obj

    def display_object(self):
        return self.display_obj

    def anchor_to(self, new_parent):
        self.parent = new_parent
        self.update_radii()

        self.object().clear_updaters()
        self.object().add_updater(lambda obj, dt: self.update_position(dt))

        return self

    def update_radii(self):
        # NOTE: This will only work for circles or ellipses.
        if self.parent is not None:
            center = self.parent.get_center()
            radius_x = (self.parent.get_width() - self.get_width()) / 2.0
            radius_y = (self.parent.get_height() - self.get_height()) / 2.0
            self.radii = np.array([radius_x, radius_y, 1])
        else:
            self.radii = np.array([0,0,1])

        return self

    def reposition(self, angle=None, offset_radius=0.5):
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

    def ready(self, val=True):
        self.is_ready = val
        return self

    def draw(self):
        if self.drawn:
            return []
        else:
            self.drawn = True
            return [ShowCreation(self.display_object())]

    def fade(self):
        if self.drawn:
            self.drawn = False
            return [FadeOut(self.display_object())]
        else:
            return []

    def update_position(self, dt):
        if self.is_ready:
            for i in range(3):
                new_x = self.object().get_x() + dt*self.speed*math.cos(self.dir)
                new_y = self.object().get_y() + dt*self.speed*math.sin(self.dir)

                if self.in_parent(new_x, new_y) and self.in_bounds():
                    self.object().move_to(np.array([new_x, new_y, 0]))
                    return self

                self.dir = random.uniform(0, 2*PI)

        return self

    def in_bounds(self):
        w = BORDER_FACTOR*FRAME_WIDTH/2
        h = BORDER_FACTOR*FRAME_HEIGHT/2
        return new_x < w and new_y < h and new_x > -w and new_y > -h

    def in_parent(self, new_x, new_y):
        if self.radii[0] == 0 or self.radii[1] == 0:
            return True
        else:
            pt = np.array([new_x, new_y, 0])
            t = (pt - self.parent.get_center()) / self.radii
            return np.dot(t, t) < self.collision_tolerance**2

class Set(Element):
    def __init__(self, elements, value=None, data=None):
        super().__init__(elements, value=value, data=data, obj_gen=lambda: VGroup([e.display_object() for e in elements]))

class Renderer(Scene):
    def construct(self):
        e1 = Element([], value=IntValue(1))
        e2 = Element([], value=IntValue(2))
        e3 = Element([], value=IntValue(3))
        self.play(*e1.draw(), *e2.draw(), *e3.draw())
        a = Set([e1, e2, e3])
        self.play(*a.draw())
        self.wait(60)
        # A = { 1,2,3 }

