From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine Assertions AssertionSemantics
  AssertionSubstitution InvariantFragment.
Import ListNotations.

(** Paper checkpoint 4B: proposed rule statements, not yet a soundness
    theorem. Nothing in the existing program calculus uses this relation.
    The grammar and interpretation of assertions are unchanged. *)
Inductive assertion_separator := SepSpatial | SepTemporal.

Definition separate kind p q :=
  match kind with SepSpatial => A.Spatial p q | SepTemporal => A.Temporal p q end.

(** An equivalence schema supplies two rules, indexed by direction. *)
Inductive assertion_direction := Forward | Backward.
Definition assertion_source direction (p q : A.assertion) :=
  match direction with Forward => p | Backward => q end.
Definition assertion_target direction (p q : A.assertion) :=
  match direction with Forward => q | Backward => p end.

Fixpoint pure_assumptions (conditions : list bexpr) : A.assertion :=
  match conditions with
  | [] => A.Pure BTrue
  | b :: rest => A.And (A.Pure b) (pure_assumptions rest)
  end.

(** No constructor takes [persistent_entails], satisfaction, safety or
    validity as a premise. The only semantic oracle concerns booleans;
    processor membership is explicit on the two qualified atomic rules. *)
Inductive assertion_derivation (active : processor_domain) : A.assertion -> A.assertion -> Prop :=
| AssertRefl p : assertion_derivation active p p
| AssertTrans p q r : assertion_derivation active p q -> assertion_derivation active q r ->
    assertion_derivation active p r
| AssertTrue p : assertion_derivation active p (A.Pure BTrue)
| AssertFalse p : assertion_derivation active (A.Pure BFalse) p
| AssertAndIntro p q r : assertion_derivation active p q -> assertion_derivation active p r ->
    assertion_derivation active p (A.And q r)
| AssertAndLeft p q : assertion_derivation active (A.And p q) p
| AssertAndRight p q : assertion_derivation active (A.And p q) q
| AssertOrLeft p q : assertion_derivation active p (A.Or p q)
| AssertOrRight p q : assertion_derivation active q (A.Or p q)
| AssertOrCases context p q result :
    assertion_derivation active (A.And context p) result ->
    assertion_derivation active (A.And context q) result ->
    assertion_derivation active (A.And context (A.Or p q)) result
| AssertExistsIntro x p expression :
    assertion_derivation active (assertion_subst x expression p) (A.Exists x p)
| AssertExistsElim context x p result : ~ In x (A.fv context ++ A.fv result) ->
    assertion_derivation active (A.And context p) result ->
    assertion_derivation active (A.And context (A.Exists x p)) result
| AssertForallIntro p x q : ~ In x (A.fv p) -> assertion_derivation active p q ->
    assertion_derivation active p (A.Forall x q)
| AssertForallElim x p expression :
    assertion_derivation active (A.Forall x p) (assertion_subst x expression p)
| AssertSubstitute x expression p q : assertion_derivation active p q ->
    assertion_derivation active (assertion_subst x expression p) (assertion_subst x expression q)
| AssertPure conditions conclusion :
    (forall s, (forall b, In b conditions -> eval_bexpr s b = true) ->
      eval_bexpr s conclusion = true) ->
    assertion_derivation active (pure_assumptions conditions) (A.Pure conclusion)
| AssertPureCases p b q :
    assertion_derivation active (A.And p (A.Pure b)) q ->
    assertion_derivation active (A.And p (A.Pure (BNot b))) q ->
    assertion_derivation active p q
| AssertEquality x expression replacement p :
    assertion_derivation active
      (A.And (A.Pure (BEq expression replacement)) (assertion_subst x expression p))
      (assertion_subst x replacement p)
| AssertSeparateMono kind p p' q q' : assertion_derivation active p p' -> assertion_derivation active q q' ->
    assertion_derivation active (separate kind p q) (separate kind p' q')
| AssertUnitLeft kind direction p :
    assertion_derivation active (assertion_source direction (separate kind A.Emp p) p)
      (assertion_target direction (separate kind A.Emp p) p)
| AssertUnitRight kind direction p :
    assertion_derivation active (assertion_source direction (separate kind p A.Emp) p)
      (assertion_target direction (separate kind p A.Emp) p)
| AssertAssociative kind direction p q r :
    assertion_derivation active
      (assertion_source direction (separate kind (separate kind p q) r) (separate kind p (separate kind q r)))
      (assertion_target direction (separate kind (separate kind p q) r) (separate kind p (separate kind q r)))
| AssertSpatialComm p q : assertion_derivation active (A.Spatial p q) (A.Spatial q p)
| AssertOrSeparateLeft kind direction p q r :
    assertion_derivation active
      (assertion_source direction (separate kind (A.Or p q) r) (A.Or (separate kind p r) (separate kind q r)))
      (assertion_target direction (separate kind (A.Or p q) r) (A.Or (separate kind p r) (separate kind q r)))
| AssertOrSeparateRight kind direction p q r :
    assertion_derivation active
      (assertion_source direction (separate kind p (A.Or q r)) (A.Or (separate kind p q) (separate kind p r)))
      (assertion_target direction (separate kind p (A.Or q r)) (A.Or (separate kind p q) (separate kind p r)))
| AssertExistsSeparateLeft kind direction x p q : ~ In x (A.fv q) ->
    assertion_derivation active
      (assertion_source direction (separate kind (A.Exists x p) q) (A.Exists x (separate kind p q)))
      (assertion_target direction (separate kind (A.Exists x p) q) (A.Exists x (separate kind p q)))
| AssertExistsSeparateRight kind direction x p q : ~ In x (A.fv p) ->
    assertion_derivation active
      (assertion_source direction (separate kind p (A.Exists x q)) (A.Exists x (separate kind p q)))
      (assertion_target direction (separate kind p (A.Exists x q)) (A.Exists x (separate kind p q)))
| AssertPureSeparateLeft kind direction b p q :
    assertion_derivation active
      (assertion_source direction (separate kind (A.And (A.Pure b) p) q) (A.And (A.Pure b) (separate kind p q)))
      (assertion_target direction (separate kind (A.And (A.Pure b) p) q) (A.And (A.Pure b) (separate kind p q)))
| AssertPureSeparateRight kind direction b p q :
    assertion_derivation active
      (assertion_source direction (separate kind p (A.And q (A.Pure b))) (A.And (separate kind p q) (A.Pure b)))
      (assertion_target direction (separate kind p (A.And q (A.Pure b))) (A.And (separate kind p q) (A.Pure b)))
| AssertSpatialWandIntro p q r : assertion_derivation active (A.Spatial p q) r ->
    assertion_derivation active q (A.SpatialWand p r)
| AssertSpatialWandElim p q r : assertion_derivation active q (A.SpatialWand p r) ->
    assertion_derivation active (A.Spatial p q) r
| AssertTemporalWandLeftIntro p q r : assertion_derivation active (A.Temporal p q) r ->
    assertion_derivation active q (A.TemporalWandLeft p r)
| AssertTemporalWandLeftElim p q r : assertion_derivation active q (A.TemporalWandLeft p r) ->
    assertion_derivation active (A.Temporal p q) r
| AssertTemporalWandRightIntro p q r : assertion_derivation active (A.Temporal q p) r ->
    assertion_derivation active q (A.TemporalWandRight r p)
| AssertTemporalWandRightElim p q r : assertion_derivation active q (A.TemporalWandRight r p) ->
    assertion_derivation active (A.Temporal q p) r
| AssertBarrierEmp annotation : assertion_derivation active (A.Barrier annotation) A.Emp
| AssertBarrierDuplicate kind direction annotation :
    assertion_derivation active
      (assertion_source direction (separate kind (A.Barrier annotation) (A.Barrier annotation)) (A.Barrier annotation))
      (assertion_target direction (separate kind (A.Barrier annotation) (A.Barrier annotation)) (A.Barrier annotation))
| AssertBarrierDistribute kind direction p q annotation :
    assertion_derivation active
      (assertion_source direction (A.Temporal (separate kind p q) (A.Barrier annotation))
        (separate kind (A.Temporal p (A.Barrier annotation)) (A.Temporal q (A.Barrier annotation))))
      (assertion_target direction (A.Temporal (separate kind p q) (A.Barrier annotation))
        (separate kind (A.Temporal p (A.Barrier annotation)) (A.Temporal q (A.Barrier annotation))))
| AssertBarrierSpatial p annotation :
    assertion_derivation active (A.Temporal p (A.Barrier annotation)) (A.Spatial p (A.Barrier annotation))
| AssertLockRight direction p annotation :
    assertion_derivation active
      (assertion_source direction (A.Temporal p (A.Lock annotation)) (A.Spatial p (A.Lock annotation)))
      (assertion_target direction (A.Temporal p (A.Lock annotation)) (A.Spatial p (A.Lock annotation)))
| AssertLockLeft direction p annotation :
    assertion_derivation active
      (assertion_source direction (A.Temporal (A.Lock annotation) p) (A.Spatial (A.Lock annotation) p))
      (assertion_target direction (A.Temporal (A.Lock annotation) p) (A.Spatial (A.Lock annotation) p))
| AssertLocksExclusive first second blocker : active blocker -> blocker <> first -> blocker <> second ->
    assertion_derivation active
      (A.Spatial (A.Lock (EVal (Z.pos first))) (A.Lock (EVal (Z.pos second)))) (A.Pure BFalse)
| AssertWritesExclusive address first second old next :
    assertion_derivation active
      (A.Spatial (A.LeadsTo address first old) (A.LeadsTo address second next)) (A.Pure BFalse)
| AssertWritesCollapse direction address annotation old next :
    assertion_derivation active
      (assertion_source direction
        (A.Temporal (A.Temporal (A.LeadsTo address annotation old) (A.LeadsTo address annotation next)) (A.Barrier annotation))
        (A.Temporal (A.LeadsTo address annotation next) (A.Barrier annotation)))
      (assertion_target direction
        (A.Temporal (A.Temporal (A.LeadsTo address annotation old) (A.LeadsTo address annotation next)) (A.Barrier annotation))
        (A.Temporal (A.LeadsTo address annotation next) (A.Barrier annotation)))
| AssertPointsToWrite address value annotation :
    (forall s, exists owner, eval_expr s annotation = Z.pos owner /\ active owner) ->
    assertion_derivation active (A.points_to address value) (A.LeadsTo address annotation value)
| AssertCellsSeparate direction address other old next :
    assertion_derivation active
      (A.And (A.Pure (BNot (BEq address other)))
        (assertion_source direction
          (A.Temporal (writer_points_to address old) (writer_points_to other next))
          (A.Spatial (writer_points_to address old) (writer_points_to other next))))
      (A.And (A.Pure (BNot (BEq address other)))
        (assertion_target direction
          (A.Temporal (writer_points_to address old) (writer_points_to other next))
          (A.Spatial (writer_points_to address old) (writer_points_to other next))))
| AssertCellOverwrite address old next :
    assertion_derivation active
      (A.Temporal (writer_points_to address old) (writer_points_to address next))
      (writer_points_to address next).
