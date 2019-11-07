Module Type Sets.

Parameter set : Type.

Axiom excluded_middle : forall (P : Prop), P \/ ~P.

Parameter elem : set -> set -> Prop.

Definition subset (x y : set) := forall (z : set), elem z x -> elem z y.

Inductive formula : Type :=
  | Eq : set -> set -> formula
  | In : set -> set -> formula
  | Neg : formula -> formula
  | And : formula -> formula -> formula
  | Or : formula -> formula -> formula
  | Forall : (set -> formula) -> formula
  | Exists : (set -> formula) -> formula.

Notation "x 'is' 'a' 'subset' 'of' y" := (subset x y) (at level 70).
Notation "x 'is' 'in' y" := (elem x y) (at level 30, no associativity).
Notation "'there' 'is' 'some' s 'so' 'that' P" := (exists (s : set), P) (at level 60).
Notation "'for' 'any' s 'holds' P" := (forall (s : set), P) (at level 60).
Notation "'for' x 'in' y , P" := (forall (x : set), x is in y -> P) (at level 70).

Notation "'there' 'is' 'some' s 'in' x 'so' 'that' P" := (exists (s : set), s is in x /\ P) (at level 60).

Notation "'there' 'is' 'unique' s 'so' 'that' P" := (
  there is some s so that (P s /\ forall (x : set), P x -> x = s)) (at level 70).

Notation "'there' 'is' 'unique' s 'in' y 'so' 'that' P" := (
  there is some s in y so that (P s /\ (for x in y, (P x -> x = s)))) (at level 70).

Lemma iff_forward : 
  forall {P1 P2 : Prop}, (P1 <-> P2) -> P1 -> P2.
Proof.
intuition.
Qed.

Lemma iff_backward :
  forall {P1 P2 : Prop}, (P1 <-> P2) -> P2 -> P1.
Proof.
intuition.
Qed.

Ltac prove := 
  do 2 (
    simpl;
    intuition;
    try congruence;
    intuition
  ).

Tactic Notation "iff" uconstr(expr) "forward" "given" uconstr(H) :=
  pose proof iff_forward expr H.

Tactic Notation "iff" uconstr(expr) "backward" "given" uconstr(H) :=
  pose proof iff_backward expr H.

Tactic Notation "iff" uconstr(expr) "given" uconstr(H) :=
  iff expr forward given H ||
  iff expr backward given H.

Tactic Notation "iff" uconstr(expr) :=
  match goal with
  | H : _ |- _ => iff expr given H (* Try every hypothesis to see if we can generate additional facts *)
  end.

Tactic Notation "follows" "from" tactic(tac) :=
  tac; prove.

Tactic Notation "disjunc" tactic(tac) :=
  (left; tac; prove) || (right; tac; prove).

Tactic Notation "sufficient" "to" "show" constr(expr) "because" tactic(tac) :=
  cut expr; only 1 : (prove; tac; prove).

Tactic Notation "sufficient" "to" "show" constr(expr) :=
  sufficient to show expr because idtac.

Tactic Notation "use" "both" tactic(tac1) "and" tactic(tac2) :=
  progress (split; ((tac1; prove) || (tac2; prove))).

Tactic Notation "follows" "by" uconstr(expr) "in" ident(H) :=
  follows from (apply expr in H).

Tactic Notation "follows" "by" uconstr(expr) :=
  follows from (apply expr) ||
  match goal with
  | H : _ |- _ => follows by expr in H
  end.

Parameter existence : set.
Parameter extensionality :
  forall {a b : set},
    ( forall (z : set), z is in a <-> z is in b ) <-> a = b.
Parameter pairing : set -> set -> set.

Notation "{ a , b }" := (pairing a b).

Parameter pairing_prop :
  forall (a b : set),
    forall (w : set), w is in {a,b} <-> (w = a \/ w = b).

Lemma left_in_pairing :
  forall (a b : set), a is in {a,b}.
Proof.
intros a b.
follows from (pose proof pairing_prop a b a).
Qed.

Lemma right_in_pairing :
  forall (a b : set), b is in {a,b}.
Proof.
intros a b.
follows from (pose proof pairing_prop a b b).
Qed.

Parameter union : set -> set.
Parameter union_prop : 
  forall (c : set),
    forall (x : set), (x is in union c <-> (there is some s so that (s is in c /\ x is in s))).
Parameter powerset : set -> set.
Parameter powerset_prop :
  forall (x : set), forall (y : set), y is in powerset x <-> y is a subset of x.
Parameter comprehension : forall (x : set) (P : set -> Prop), set.

Notation "{ x ; P }" := (comprehension x P) (no associativity).
Notation "{ y 'in' x ; P }" := (comprehension x (fun y => P)).

Parameter comprehension_prop :
  forall (P : set -> Prop),
    forall (x z : set), z is in { x ; P } <-> (z is in x /\ P z).

Definition emptyset : set := { x in existence ; x <> x }.

Lemma elem_comprehension : 
  forall {P : set -> Prop} {x z : set}, z is in { x ; P } -> P z.
Proof.
intros.
follows from (iff (comprehension_prop P x z) given H).
Qed.

Tactic Notation "use" "comprehension" "for" uconstr(v) :=
  pose proof elem_comprehension v.

Tactic Notation "contradiction" "by" tactic(tac) :=
  tac; prove; contradiction.

Definition empty (X : set) : Prop :=
  forall (Y : set), ~(Y is in X).

Lemma emptyset_is_empty : empty emptyset.
Proof.
intros z zinemptyset.
contradiction by (use comprehension for zinemptyset).
Qed.

Notation "'U' C" := (union C) (at level 70).

(* Note: The following are both useful helpers and also proofs that such sets exist *)
Definition pair_union (a b : set) : set := U {a,b}.
Definition singleton (a : set) : set := {a,a}.

Notation "a 'U' b" := (pair_union a b) (at level 80).

Lemma in_pair_union_forward :
  forall (a b c : set), c is in (a U b) -> c is in a \/ c is in b.
Proof.
intros.
unfold pair_union.
iff (union_prop (pairing a b) c).
destruct H0; destruct H0.
iff (pairing_prop a b x).
inversion H2.
follows from (left; rewrite <- H3).
follows from (right; rewrite <- H3).
Qed.

Lemma in_pair_union_backward :
  forall (a b c : set), c is in a \/ c is in b -> c is in (a U b).
Proof.
intros.
unfold pair_union.
intros.

cut (there is some s so that (s is in pairing a b /\ c is in s)).
intro.
follows from (iff (union_prop (pairing a b) c)).

inversion H.
- follows from (exists a; split; apply left_in_pairing || intuition).
- follows from (exists b; split; apply right_in_pairing || intuition).
Qed.

Lemma pair_union_prop :
  forall {a b c : set}, c is in (a U b) <-> c is in a \/ c is in b.
Proof.
intros.
follows from (split; apply in_pair_union_forward || apply in_pair_union_backward).
Qed.

Lemma in_singleton : forall (x : set), x is in singleton x.
Proof.
intros.
follows from (unfold singleton; apply pairing_prop).
Qed.

Lemma singleton_contains_unique : forall {x y : set}, x is in singleton y <-> x = y.
Proof.
intros.
split.
- follows from (intros; iff (pairing_prop y y x)).
- follows from (intro Eq; rewrite Eq; pose proof pairing_prop y y y).
Qed.

Lemma singleton_eq : forall {x y : set}, singleton x = singleton y <-> x = y.
Proof.
intros.
split.
- intros.
follows from (apply singleton_contains_unique; rewrite <- H; apply in_singleton).
- intros. 
follows from (rewrite H).
Qed.

Definition successor (x : set) := x U (singleton x).

Parameter infinity : set.
Parameter infinity_prop :
  elem emptyset infinity /\ (forall (n : set), successor n is in infinity).

Lemma both_include_eq : 
  forall (x y : set), x is a subset of y -> y is a subset of x -> x = y.
Proof.
intros x y x_sub_y y_sub_x.
apply extensionality.
split.
- apply x_sub_y.
- apply y_sub_x.
Qed.

Definition nonempty (x : set) := there is some y so that y is in x.

Parameter foundation :
  forall (x : set),
    nonempty x ->
      there is some y so that (y is in x /\ ~(there is some z so that (z is in x /\ z is in y))).

Definition function_formula (x : set) (P : set -> set -> Prop) :=
  forall (z : set), z is in x -> (there is unique y so that P z).

Parameter replacement : set -> (set -> set -> Prop) -> set.
Parameter replacement_prop :
  forall (x : set) (P : set -> set -> Prop), 
    function_formula x P -> 
        forall (z : set), z is in x -> (
          there is some w so that (w is in (replacement x P) /\ P z w)).

Definition intersection (c : set) : set := { y in U c ; for s in c, y is in s }.

Definition ordered_pair (x y : set) := {singleton x, {x, y}}.

Notation "( x , y )" := (ordered_pair x y) (no associativity).

Lemma elem_dif_set_dif :
  forall (x y : set), 
    (there is some z so that (z is in x /\ ~(z is in y))) -> x <> y.
Proof.
intros.
destruct H; destruct H.
intros x_eq_y.
iff extensionality given x_eq_y.
contradiction by (pose proof H1 x0).
Qed.

Lemma singleton_in_ordered_pair :
  forall {x y : set}, singleton x is in (x, y).
Proof.
intros.
follows from (apply left_in_pairing).
Qed.

Lemma pairing_in_ordered_pair :
  forall {x y : set}, {x, y} is in (x, y).
Proof.
intros.
follows from (apply right_in_pairing).
Qed.

Lemma pairing_is_singleton_eq :
  forall {x y : set}, singleton x = {x,y} <-> x = y.
Proof.
intros.
split.
- intros.
pose proof right_in_pairing x y as y_in_pairing.
follows from (rewrite <- H in y_in_pairing; pose proof (@singleton_contains_unique y x)).
- intros.
follows from (rewrite H).
Qed.

Lemma pairing_commutes :
  forall {x y : set}, {x,y} = {y,x}.
Proof.
intros x y.
apply extensionality.
intros z.
split; intros H; follows from (apply pairing_prop; apply pairing_prop in H).
Qed.

Lemma singleton_is_pair_then_pair_same :
  forall (x y z : set), singleton x = {y,z} <-> x = y /\ y = z.
Proof.
intros.
split.
- intros.
pose proof in_singleton x as is_in_sing_x.
rewrite H in is_in_sing_x.
apply pairing_prop in is_in_sing_x.
inversion is_in_sing_x.
rewrite H0 in H; follows from (iff (@pairing_is_singleton_eq y z)).
rewrite H0, pairing_commutes in H; follows from (iff (@pairing_is_singleton_eq z y)).
- intros.
intuition.
follows from (rewrite H0, H1; apply pairing_is_singleton_eq).
Qed.

Lemma in_in_col_in_union :
  forall (a b c : set), a is in b -> b is in c -> a is in U c.
Proof.
intros a b c a_in_b b_in_c.
pose proof union_prop c a.
sufficient to show (there is some s so that (s is in c /\ a is in s)).
follows from (exists b).
Qed.

Lemma in_col_is_subset_of_union :
  forall (a c : set), a is in c -> a is a subset of U c.
Proof.
intros.
unfold subset.
intros.
follows from (apply (in_in_col_in_union z a c)).
Qed.

Lemma singleton_subset_is_elem :
  forall (a b : set), singleton a is a subset of b -> a is in b.
Proof.
intros.
follows from (pose proof H a (in_singleton a)).
Qed.

Lemma ordered_pair_contains_one_singleton :
  forall (x y z : set), singleton x is in (y,z) -> x = y.
Proof.
intros.
apply pairing_prop in H.
inversion H.
- follows from (iff singleton_eq given H0).
- sufficient to show (singleton x = singleton y) because 
    (repeat (follows from (iff (@singleton_eq x y)))).
follows from (apply singleton_is_pair_then_pair_same in H0).
Qed.

Lemma ordered_pair_contains_one_pair :
  forall (a b c d : set), {a, b} is in (c,d) -> (a = b /\ a = c) \/ {a,b} = {c,d}.
Proof.
intros a b c d ab_in_cd.
apply pairing_prop in ab_in_cd.
inversion ab_in_cd.
- left. symmetry in H.
follows by singleton_is_pair_then_pair_same.
- prove.
Qed.

Lemma ordered_pair_is_ordered :
  forall {x y : set}, (x, y) = (y, x) -> x = y.
Proof.
intros x y pair_eq.
iff extensionality given pair_eq.

iff (H (singleton x)) given (left_in_pairing (singleton x) (pairing x y)).
apply pairing_prop in H0.

destruct H0.
- follows from (apply singleton_eq).
- follows from (apply pairing_is_singleton_eq; rewrite pairing_commutes).
Qed.

Lemma ordered_pair_same :
  forall {a : set}, (a, a) = singleton (singleton a).
Proof.
intuition.
Qed.

Lemma pairing_in_nested_singleton :
  forall {a b c : set}, {a, b} is in (singleton (singleton c)) -> a = c /\ b = c.
Proof.
intros a b c containment.
apply singleton_contains_unique, eq_sym in containment.
follows by singleton_is_pair_then_pair_same.
Qed.

Lemma pairing_eq_cases :
  forall {a b c d : set}, {a,b} = {c,d} -> (a = c \/ a = d) /\ (b = c \/ b = d).
Proof.
intros a b c d ab_eq_cd.
pose proof left_in_pairing a b as a_in_ab.
pose proof right_in_pairing a b as b_in_ab.
rewrite ab_eq_cd in a_in_ab, b_in_ab.
apply pairing_prop in a_in_ab.
apply pairing_prop in b_in_ab.
intuition.
Qed.

Lemma pairing_eq :
  forall (a b c d : set), {a,b} = {c,d} -> (a = c /\ b = d) \/ (a = d /\ b = c).
Proof.
intros a b c d ab_eq_cd.
pose proof pairing_eq_cases ab_eq_cd.
inversion H.

inversion H0.

- inversion H1.
-- left; prove.
rewrite H2, H3 in ab_eq_cd.
follows from (iff (@pairing_is_singleton_eq c d)).
-- prove.

- inversion H1.
-- prove.
-- rewrite H2, H3, (@pairing_commutes c d) in ab_eq_cd.
follows from (right; iff (@pairing_is_singleton_eq d c)).
Qed.

Tactic Notation "rewrite_conj" hyp(expr) :=
  destruct expr as [?l ?r]; rewrite ?l, ?r.

Tactic Notation "rewrite_conj" "<-" hyp(expr) :=
  destruct expr as [?l ?r]; rewrite <- ?l, <- ?r.

Tactic Notation "rewrite_conj" hyp(expr) "in" hyp(H) :=
  destruct expr as [?l ?r]; rewrite ?l, ?r in H.

Tactic Notation "rewrite_conj" "<-" hyp(expr) "in" hyp(H) :=
  destruct expr as [?l ?r]; rewrite <- ?l, <- ?r in H.

Lemma ordered_pair_eq :
  forall (a b c d : set), (a, b) = (c, d) -> a = c /\ b = d.
Proof.
intros a b c d ab_eq_cd.
pose proof iff_backward extensionality ab_eq_cd as in_pair.
split.
- iff (in_pair (singleton a)) given singleton_in_ordered_pair.
follows by ordered_pair_contains_one_singleton.
-
iff (in_pair (pairing a b)) given pairing_in_ordered_pair.
apply ordered_pair_contains_one_pair in H.
inversion H.
-- rewrite_conj H0 in in_pair.
iff (in_pair (pairing c d)) given pairing_in_ordered_pair.
follows by pairing_in_nested_singleton.
-- apply pairing_eq in H0; prove.
rewrite H0, H2 in ab_eq_cd.
follows by ordered_pair_is_ordered.
Qed.

Definition cart_prod_formula (X Y : set) (p : set) : Prop := 
  there is some x in X so that (there is some y in Y so that (p = (x,y))).
Definition cart_prod (X Y : set) : set :=
  { p in powerset (powerset (X U Y)) ; cart_prod_formula X Y p}.

Lemma cart_prod_base_set_prop :
  forall {X Y x y : set}, x is in X -> y is in Y -> (x,y) is in powerset (powerset (X U Y)).
Proof.
intros X Y x y x_in_X y_in_Y.
apply powerset_prop.
unfold subset.
intros z z_in_pair.
apply powerset_prop.
unfold subset.
intros w w_in_z.
apply pair_union_prop.

apply pairing_prop in z_in_pair.
inversion z_in_pair.
- rewrite H in w_in_z.
follows from (left; iff singleton_contains_unique given w_in_z).

- rewrite H in w_in_z.
apply pairing_prop in w_in_z.
inversion w_in_z.
follows from left.
follows from right.
Qed.

Lemma cart_prod_formula_holds :
  forall {X Y x y : set}, x is in X -> y is in Y -> cart_prod_formula X Y (x,y).
Proof.
intros X Y x y x_in_X y_in_Y.
exists x; prove.
exists y; prove.
Qed.

Lemma cart_prod_prop_subset :
  forall {X Y x y : set}, x is in X -> y is in Y -> (x,y) is in cart_prod X Y.
Proof.
intros X Y x y x_in_X y_in_Y.
apply comprehension_prop.
use both (apply cart_prod_base_set_prop) and (apply cart_prod_formula_holds).
Qed.

Lemma cart_prod_prop_supset :
  forall {X Y x y : set}, (x,y) is in cart_prod X Y -> x is in X /\ y is in Y.
Proof.
intros X Y x y xy_in_prod.
use comprehension for xy_in_prod; simpl in H.
repeat destruct H; repeat destruct H0.
follows by ordered_pair_eq.
Qed.

Lemma cart_prod_prop_pairs :
  forall {X Y x y : set}, (x,y) is in cart_prod X Y <-> x is in X /\ y is in Y.
Proof.
intros.
split.
- apply cart_prod_prop_supset.
- intros; follows by cart_prod_prop_subset.
Qed.

Lemma cart_prod_prop :
  forall {X Y z : set}, 
    z is in cart_prod X Y <-> 
    there is some x in X so that (there is some y in Y so that (z = (x,y))).
Proof.
intros.
split.
- intros z_in_prod.
apply comprehension_prop in z_in_prod.
apply proj2 in z_in_prod.
intuition.
- intros z_is_pair.
destruct z_is_pair, H, H0, H0.
rewrite H1.
follows by cart_prod_prop_pairs.
Qed.

Definition is_function (dom : set) (codom : set) (f : set) : Prop := 
  f is a subset of (cart_prod dom codom) /\
  forall (x : set), x is in dom -> there is unique y in codom so that (fun y => (x,y) is in f).

Definition compatible (dom codom f : set) (actual : set -> set) : Prop :=
  for x in dom, (x, actual x) is in f.

Inductive function (dom codom : set) : Type :=
  | func (f : set) (actual : set -> set) :
      compatible dom codom f actual -> is_function dom codom f -> function dom codom.

Definition do_fst (X Y xy : set) : xy is in cart_prod X Y -> set.
intros xy_in_prod.
apply cart_prod_prop in xy_in_prod.
destruct xy_in_prod.

Definition fst : function X Y :=
  func 
  { xy in cart_prod (cart_prod X Y) X;
    there is some x in X, there is some y in Y, (xy = ((x,y),x)) }
  (fun 

Definition functions (dom : set) (codom : set) : set :=
  { f in powerset (cart_prod dom codom) ; is_function dom codom f }.

Lemma functions_prop_supset :
  forall (dom codom f : set), is_function dom codom f -> f is in functions dom codom.
Proof.
intros.
apply comprehension_prop.
split.
- apply powerset_prop.
unfold subset.
intros z z_in_f.
destruct H.
prove.
- prove.
Qed.

Lemma functions_prop :
  forall (dom codom f : set), f is in functions dom codom <-> is_function dom codom f.
Proof.
intros.
split.
- follows by comprehension_prop. (* True simply by using the comprehension formula *)
- follows by functions_prop_supset.
Qed.

Definition apply {X Y : set} (f : function X Y) (x : set) : set :=
  match f with
  | func _ _ _ actual _ _ => actual x
  end.

Notation "f [ x ]" := (apply f x) (at level 10).

Lemma apply_compat :
  forall {X Y : set} (f : function X Y),
    for x in X, (f[x] is in Y).
Proof.
intros X Y f x x_in_X.
destruct f.
destruct i.
pose proof s (x, actual x) (c x x_in_X).
apply cart_prod_prop in H.
destruct H, H, H0, H0.
follows by ordered_pair_eq.
Qed.

Definition underlying_set {X Y : set} (f : function X Y) : set :=
  match f with
  | func _ _ f_set _ _ _ => f_set
  end.

Definition rep_prop {X Y : set} (f : function X Y) (x y : set) : Prop :=
  match f with
  | func _ _ f_set _ _ _ => (x,y) is in f_set
  end.

Lemma use_uniqueness :
  forall {P : set -> Prop} {x y : set},
    there is unique z so that P -> P x -> P y -> x = y.
Proof.
intros P x y uniq Px Py.
destruct uniq, H.
pose proof H0 x Px.
pose proof H0 y Py.
prove.
Qed.

Lemma use_uniqueness_in :
  forall {P : set -> Prop} {A x y : set},
    there is unique a in A so that P ->
    x is in A -> P x -> y is in A -> P y ->
    x = y.
Proof.
intros P A x y uniq x_in_A Px y_in_A Py.
destruct uniq, H, H0.
pose proof H1 x x_in_A Px.
pose proof H1 y y_in_A Py.
prove.
Qed.

Lemma func_unique_map :
  forall {X Y : set} (f : set),
    for x in X, for y1 in Y, for y2 in Y, 
      (is_function X Y f -> (x, y1) is in f -> (x, y2) is in f -> y1 = y2).
Proof.
intros X Y f x x_in_X y1 y1_in_Y y2 y2_in_Y is_func y1_in_f y2_in_f.
destruct is_func.
pose proof H0 x x_in_X.
follows by (@use_uniqueness_in (fun k => (x,k) is in f) Y).
Qed.

Lemma rep_prop_compat :
  forall {X Y : set} (f : function X Y),
    for x in X, for y in Y, (rep_prop f x y -> f[x] = y).
Proof.
intros X Y f x x_in_X y y_in_Y rep_prop.
destruct f.
simpl.
simpl in rep_prop.
pose proof c x x_in_X.
destruct i.
pose proof H1 x x_in_X.
pose proof H0 (x, actual x) H.
apply cart_prod_prop_pairs in H3.
follows by (@use_uniqueness_in (fun k => (x,k) is in f) Y).
Qed.

Lemma for_any_is_for_in :
  forall (P : set -> Prop),
    (forall (x : set), P x) -> (forall (Y : set), for x in Y, P x).
Proof.
prove.
Qed.

Lemma rep_prop_is_function_formula :
  forall {X Y : set} (f : function X Y), function_formula X (rep_prop f).
Proof.
intros X Y f x x_in_X.
destruct f, i.
pose proof e x x_in_X.
simpl.
destruct H, H.
exists x0.
prove.
pose proof s (x, x1) H0.
apply cart_prod_prop_pairs in H3.
destruct H3.
exact (H2 x1 H4 H0).
Qed.

Definition replacement_im (X : set) (P : set -> set -> Prop) (prf : function_formula X P) : set :=
  { y in replacement X P; there is some x in X so that (P x y) }.

Definition im {X Y : set} (f : function X Y) (A : set) {prf : A is a subset of X} : set := 
  replacement_im X (rep_prop f) (rep_prop_is_function_formula f).

Lemma in_subset_in_supset :
  forall {X Y : set}{a : set}, X is a subset of Y -> a is in X -> a is in Y.
Proof.
prove.
Qed.

Lemma in_subset_of_cart_prod :
  forall {X Y : set} {x y A : set}, 
    A is a subset of cart_prod X Y -> (x, y) is in A -> (x is in X /\ y is in Y).
Proof.
intros.
apply (in_subset_in_supset H) in H0.
follows by cart_prod_prop_supset.
Qed.

Lemma function_is_subset :
  forall {X Y f : set}, is_function X Y f -> f is a subset of cart_prod X Y.
Proof.
intros X Y f is_func.
follows from (destruct is_func).
Qed.

Lemma rep_prop_in_codom :
  forall {X Y : set} {f : function X Y} {x y : set}, rep_prop f x y -> y is in Y.
Proof.
intros X Y f x y rep_prop_f_x_y.
destruct f; simpl in rep_prop_f_x_y.
apply function_is_subset in i.
follows by (in_subset_of_cart_prod i).
Qed.

Lemma im_prop_supset :
  forall {X Y : set} (f : function X Y) (A y : set) {prf : A is a subset of X}, 
    y is in (@im X Y f A prf) -> there is some x in X so that (f[x] = y).
Proof.
intros X Y f A y prf y_in_im.
apply comprehension_prop in y_in_im.
destruct y_in_im as [y_in_rep exist_x],
         exist_x as [x x_func],
         x_func as [x_in_X f_x_is_y].
exists x.
split; prove.
- apply rep_prop_compat; prove.
-- apply rep_prop_in_codom in f_x_is_y; prove.
Qed.

Inductive relation (X Y : set) : Type :=
  | rel (x : set) : x is a subset of cart_prod X Y -> relation X Y.

Definition related {X Y : set} (R : relation X Y) (x y : set) :=
  match R with
  | rel _ _ underlying _ => (x, y) is in underlying
  end.

Definition binary_rel (X : set) := relation X X.

Definition irrefl {X : set} (R : binary_rel X) :=
  for x in X, ~(related R x x).

Definition transitive {X : set} (R : binary_rel X) :=
  for x in X, for y in X, for z in X, 
    (related R x y -> related R y z -> related R x z).

Inductive partial_ord (X : set) : Type :=
  | partial (R : binary_rel X) :
      irrefl R -> transitive R -> partial_ord X.

Definition transitive_set (x : set) : Prop :=
  for y in x, (y is a subset of x).

Definition partial_related {X : set} (P : partial_ord X) (x y : set) :=
  match P with
  | partial _ R _ _ => related R x y
  end.

Definition total_ord_prop {X : set} (P : partial_ord X) :=
  for x in X, for y in X,
    ((partial_related P x y) \/ (x = y) \/ (partial_related P y x)).

Inductive total_ord (X : set) : Type :=
  | total (R : partial_ord X) : total_ord_prop R -> total_ord X.

Definition total_related {X : set} (T : total_ord X) (x y : set) :=
  match T with
  | total _ R _ => partial_related R x y
  end.

Definition setminus (X : set) (Y : set) : set :=
  { x in X; x is in X /\ ~(x is in Y) }.

Notation "X \ Y" := (setminus X Y) (at level 70).

Lemma setminus_prop :
  forall {X Y x : set}, x is in (X \ Y) -> x is in X /\ ~(x is in Y).
Proof.
intros X Y x x_in_setminus.
follows by comprehension_prop.
Qed.

Definition nonempty_powerset (X : set) : set :=
  powerset X \ singleton emptyset.

Definition singleton_is_subset_iff_elem :
  forall {X x : set}, x is in X <-> singleton x is a subset of X.
Proof.
intros X x.
split.
- intros x_in_X z z_in_x.
follows by singleton_contains_unique.
- intros sing_x_subs_X.
exact (sing_x_subs_X x (in_singleton x)).
Qed.

Lemma nonempty_has_nonempty_powerset :
  forall (X : set), nonempty X -> nonempty (powerset X).
Proof.
intros X nonempty_X.
destruct nonempty_X as [x x_in_X].
exists (singleton x).
follows from (apply powerset_prop, singleton_is_subset_iff_elem).
Qed.

Lemma in_emptyset_absurd :
  forall {x : set}, ~(x is in emptyset).
Proof.
intros x x_in_emptyset.
pose proof emptyset_is_empty x x_in_emptyset.
contradiction.
Qed.

Lemma empty_iff_emptyset : 
  forall (X : set), X = emptyset <-> empty X.
Proof.
intros X.
split.
- intros X_is_emptyset.
rewrite X_is_emptyset.
apply emptyset_is_empty.
- intros X_empty.
apply extensionality.
intros z.
split.
-- intros z_in_X.
follows from (pose proof X_empty z z_in_X).
-- intros z_in_emptyset.
follows from (pose proof in_emptyset_absurd z_in_emptyset).
Qed.

Lemma not_in_sing_empty_is_not_empty :
  forall (Y : set), ~(Y is in singleton emptyset) -> ~(empty Y).
Proof.
intros Y not_in_sing_empty empty_Y.
apply empty_iff_emptyset in empty_Y.
rewrite empty_Y in not_in_sing_empty.
pose proof in_singleton emptyset.
contradiction.
Qed.

(* TODO: We can't say Y is nonempty, only that ~(empty Y)...excluded middle issues. Should we cave and use it? *)
Lemma in_nonempty_powerset_is_not_empty :
  forall (X Y : set), Y is in nonempty_powerset X -> ~(empty Y).
Proof.
intros X Y in_ne_powset empty_Y.
apply comprehension_prop, proj2, proj2, not_in_sing_empty_is_not_empty in in_ne_powset.
contradiction.
Qed.

Definition choice_function {X : set} (f : function (nonempty_powerset X) X) : Prop :=
  forall (Y : set), nonempty Y -> Y is a subset of X -> f[Y] is in Y.

Definition well_ord_prop {X : set} 
                         (T : total_ord X) 
                         (min : function (nonempty_powerset X) X) :=
  forall (Y : set) (nonempty_Y : nonempty Y) (Y_subs_X : Y is a subset of X),
    (for y in Y, ~(total_related T y (min[Y]))) /\
    (min[Y]) is in Y.

Lemma nonempty_is_not_empty :
  forall {X : set}, nonempty X -> ~(empty X).
Proof.
intros X nonempty_X empty_X.
destruct nonempty_X as [x x_in_X].
pose proof empty_X x x_in_X.
contradiction.
Qed.

Inductive well_order (X : set) : Type :=
  | well (R : total_ord X) 
         (min : function (nonempty_powerset X) X)
    : well_ord_prop R min -> well_order X.

Definition well_order_min {X : set} (W : well_order X) :=
  match W with
  | well _ _ min _ => min
  end.

Definition least {X : set} (W : well_order X) (Y : set) : set :=
  match W with
  | well _ _ min _ => min[Y]
  end.

Notation "P 'min'" := (well_order_min P) (at level 70).

Notation "P 'least' 'in' A" := (least P A) (no associativity, at level 70).

Lemma min_is_choice_function :
  forall {X : set} (W : well_order X), choice_function (W min).
Proof.
intros X W Y nonempty_Y Y_subs_X.
destruct W.
pose proof w Y nonempty_Y Y_subs_X.
prove.
Qed.

Definition well_related {X : set} (W : well_order X) (x y : set) :=
  match W with
  | well _ R _ _ => total_related R x y
  end.

Notation "x 'is' P 'less' 'than' y" := (well_related P x y) (no associativity, at level 70).


Definition inclusion_rel (X : set) : binary_rel X :=
  { a in cart_prod X X; fst[a] is in snd[a] }.
  

Definition included_ordered (x : set) : Prop :=
  total_ord 

Inductive ordinal :=
  | ord (x : set) : transitive_set x -> inclusion_ordered x -> ordinal.

Lemma emptyset_trans : transitive_set emptyset.
Proof.
intros x x_in_emptyset.
follows by in_emptyset_absurd.
Qed.

Definition set_succ (x : set) : set := x U singleton x.

Tactic Notation "use" "transitivity" "to" "get" constr(z) "in" constr(x) :=
  match goal with
  | [ x_trans : transitive_set x,
      z_in_y : z is in ?y,
      y_in_x : ?y is in x |- _ ] => 
    pose proof (in_subset_in_supset (x_trans y y_in_x) z_in_y)
  end.

Lemma set_succ_transitive_is_transitive :
  forall {x : set}, transitive_set x -> transitive_set (set_succ x).
Proof.
intros x x_trans.
intros y y_in_succ_x.
intros z z_in_y.
apply pair_union_prop in y_in_succ_x.
inversion y_in_succ_x.
- use transitivity to get z in x.
follows by pair_union_prop.
- apply singleton_contains_unique in H.
rewrite H in z_in_y.
follows by pair_union_prop.
Qed.

Definition ord_succ (x : ordinal) : ordinal := 
  match x with
  | ord s trans_prf => ord (set_succ s) (set_succ_transitive_is_transitive trans_prf)
  end.

Definition zero : ordinal := ord emptyset emptyset_trans.
Definition one : ordinal := ord_succ zero.
Definition two : ordinal := ord_succ one.

Fixpoint nth_ordinal (n : nat) : ordinal :=
  match n with
  | O => zero
  | S k => ord_succ (nth_ordinal k)
  end.

Definition injection {X Y : set} (f : function X Y) : Prop :=
  for x in X, for y in Y, (f[x] = f[y] -> x = y).

Definition surjection {X Y : set} (f : function X Y) : Prop :=
  for y in Y, (there is some x in X so that (f[x] = y)).

Definition bijection {X Y : set} (f : function X Y) : Prop :=
  injection f /\ surjection f.

Definition proper_subset (X Y : set) : Prop :=
  X is a subset of Y /\ nonempty (Y \ X).

Lemma subset_trans :
  forall {X Y Z : set}, X is a subset of Y -> Y is a subset of Z -> X is a subset of Z.
Proof.
intros X Y Z X_subs_Y Y_subs_Z.
intros x x_in_X.
prove.
Qed.

Definition pred (x X : set) (W : well_order X) (x_in_X : x is in X) : set :=
  { y in X; y is W less than x }.

Definition initial_segment (X Y : set) (W : well_order Y) : Prop :=
  X is a subset of Y /\
  forall (x : set) (x_in_Y : x is in Y), pred x Y W x_in_Y is a subset of X.

Notation "X 'is' 'a' 'proper' 'subset' 'of' Y" := (proper_subset X Y) (at level 70).

Definition proper_initial_segment (X Y : set) (W : well_order Y) : Prop :=
  initial_segment X Y W /\ X is a proper subset of Y /\ nonempty X.

Lemma nonempty_subset_is_nonempty :
  forall {X Y : set}, nonempty X -> X is a subset of Y -> nonempty Y.
Proof.
intros X Y nonempty_X X_subs_Y.
destruct nonempty_X as [x x_in_X].
exists x.
prove.
Qed.

Lemma comprehension_subset :
  forall {P : set -> Prop} {X : set}, { X; P } is a subset of X.
Proof.
intros P X y.
apply comprehension_prop.
Qed.

Lemma setminus_is_subset :
  forall (X Y : set), (X \ Y) is a subset of X.
Proof.
intros X Y.
apply comprehension_subset.
Qed.

Lemma proper_subset_is_subset :
  forall {X Y : set}, X is a proper subset of Y -> X is a subset of Y.
Proof.
intros X Y X_prop_subs_Y.
intros z z_in_X.
destruct X_prop_subs_Y.
prove.
Qed.

Definition intersect (A : set) (B : set) : set :=
  { x in A U B; x is in A /\ x is in B }.

Lemma intersect_prop :
  forall {A B x : set}, x is in intersect A B <-> x is in A /\ x is in B.
Proof.
intros A B x.
split.
- apply comprehension_prop.
- intros x_in_both.
destruct x_in_both as [x_in_A x_in_B].
apply comprehension_prop.
prove.
apply pair_union_prop.
prove.
Qed.

Lemma intersect_is_subset_left :
  forall (A B : set), intersect A B is a subset of A.
Proof.
intros A B x x_in_int.
apply comprehension_prop in x_in_int.
prove.
Qed.

Lemma intersect_is_subset_right :
  forall (A B : set), intersect A B is a subset of B.
Proof.
intros A B x x_in_int.
apply comprehension_prop in x_in_int.
prove.
Qed.

Tactic Notation "use" "subset" "to" "get" constr(z) "in" constr(x) :=
  match goal with
  | [ z_in_y : z is in ?y,
      y_subs_x : ?y is a subset of x |- _ ] => 
    pose proof (y_subs_x z z_in_y)
  | [ z_in_y : z is in ?y,
      y_prop_subs_x : ?y is a proper subset of x |- _ ] =>
    pose proof (proper_subset_is_subset y_prop_subs_x z z_in_y)
  | [ z_in_y : z is in intersection ?y x |- _ ] =>
    pose proof (intersect_is_subset_right y x z z_in_y)
  | [ z_in_y : z is in intersection x ?y |- _ ] =>
    pose proof (intersect_is_subset_left y x z z_in_y)
  | [ z_in_y : z is in (x \ ?y) |- _ ] =>
    pose proof (setminus_is_subset x y z z_in_y)
  end.

Lemma exists_least_not_in_proper_subset :
  forall {X Y : set} {W : well_order Y},
    X is a proper subset of Y -> (W least in (Y \ X)) is in Y.
Proof.
intros X Y W X_prop_subs_Y.
destruct X_prop_subs_Y as [X_subs_Y nonempty_dif].
destruct W.
pose proof setminus_is_subset Y X as dif_subset.
pose proof proj2 (w (Y \ X) nonempty_dif dif_subset).
simpl.
prove.
Qed.

Lemma initial_seg_bounded :
  forall {X Y y : set} {W : well_order Y},
    initial_segment X Y W -> y is in (Y \ X) -> forall (x : set), x is in X -> x is W less than y.
Proof.
intros X Y y W init_seg y_in_dif x x_in_X.
destruct init_seg as [X_subs_Y init_seg_prop].
use subset to get y in Y.
pose proof init_seg_prop y H.

Lemma proper_initial_segment_is_pred :
  forall {X Y : set} {W : well_order Y},
    proper_initial_segment X Y W -> (exists (x : set) (x_in_Y : x is in Y), X = pred x Y W x_in_Y).
Proof.
intros X Y W prop_init_seg.
destruct prop_init_seg as [init_seg rest],
         rest as [X_prop_subs_Y nonempty_X].
exists (W least in (Y \ X)).
exists (exists_least_not_in_proper_subset X_prop_subs_Y).
apply extensionality.
intros z.
split.
- intros z_in_X.
apply comprehension_prop.
use subset to get z in Y; prove.

End Sets.
