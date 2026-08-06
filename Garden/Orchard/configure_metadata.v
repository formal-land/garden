(** * VK-relevant Orchard configure metadata

    The constraint AST deliberately omits Halo 2 builder bookkeeping that
    has no effect on gate evaluation.  This explicit formal trace records
    that bookkeeping in the same configure program: typed allocation order,
    selector kind, first-query order, equality-enabled columns, constants,
    and the optional minimum degree.  [Metadata.run] validates typed indices
    while reproducing the ordered, deduplicating state updates of Rust's
    [ConstraintSystem].  Equality of the resulting state with Rust is an
    external configure-JSON translation-validation check. *)

Require Import Garden.Halo2.main.
Require Import Garden.Orchard.columns.

Import ListNotations.

Module OrchardConfigureMetadata.

Definition indices : Metadata.IndexMap.t columns := {|
  Metadata.IndexMap.selector := Index.selector;
  Metadata.IndexMap.fixed := Index.fixed;
  Metadata.IndexMap.lookup := Index.lookup;
  Metadata.IndexMap.advice := Index.advice;
  Metadata.IndexMap.instance_ := Index.instance_;
|}.

Definition selector_kind (selector : Selector.t) : Metadata.SelectorKind.t :=
  match selector with
  | Selector.QLookup
  | Selector.QRunning
  | Selector.QSinsemilla1_1
  | Selector.QSinsemilla1_2 => Metadata.SelectorKind.Complex
  | _ => Metadata.SelectorKind.Simple
  end.

Definition allocation_operations : list (Metadata.Operation.t columns) :=
  List.map Metadata.Operation.AllocateAdvice Advice.all ++
  (* Lookup-table columns consume fixed indices 0, 1, and 2. *)
  List.map Metadata.Operation.AllocateLookupTable Lookup.all ++
  List.map Metadata.Operation.AllocateFixed Fixed.all ++
  List.map Metadata.Operation.AllocateInstance Instance_.all ++
  List.map
    (fun selector => Metadata.Operation.AllocateSelector selector
      (selector_kind selector))
    Selector.all.

(** Current-rotation advice queries 0..9 are registered by
    [enable_equality].  These are the remaining first query occurrences in
    Halo 2 keygen order. *)
Definition rotated_advice_queries : list (Metadata.Operation.t columns) := [
  Metadata.Operation.QueryAdvice Advice.A9 Rotation.next;
  Metadata.Operation.QueryAdvice Advice.A9 Rotation.prev;
  Metadata.Operation.QueryAdvice Advice.A2 Rotation.next;
  Metadata.Operation.QueryAdvice Advice.A3 Rotation.next;
  Metadata.Operation.QueryAdvice Advice.A4 Rotation.next;
  Metadata.Operation.QueryAdvice Advice.A5 Rotation.next;
  Metadata.Operation.QueryAdvice Advice.A0 Rotation.next;
  Metadata.Operation.QueryAdvice Advice.A1 Rotation.next;
  Metadata.Operation.QueryAdvice Advice.A7 Rotation.next;
  Metadata.Operation.QueryAdvice Advice.A8 Rotation.next;
  Metadata.Operation.QueryAdvice Advice.A6 Rotation.prev;
  Metadata.Operation.QueryAdvice Advice.A1 Rotation.prev;
  Metadata.Operation.QueryAdvice Advice.A6 Rotation.next;
  Metadata.Operation.QueryAdvice Advice.A7 Rotation.prev;
  Metadata.Operation.QueryAdvice Advice.A8 Rotation.prev
].

(** Fixed-query first occurrences.  [enable_constant] registers fixed 3;
    equality on the three fixed-base window columns registers 8, 9, and 10.
    Selector compression later appends the generated fixed queries 14..28. *)
Definition fixed_query_operations : list (Metadata.Operation.t columns) := [
  Metadata.Operation.QueryLookup Lookup.TableIdx;
  Metadata.Operation.QueryFixed Fixed.FixedZ;
  Metadata.Operation.QueryFixed Fixed.LagrangeCoeffs1;
  Metadata.Operation.QueryFixed Fixed.LagrangeCoeffs2;
  Metadata.Operation.QueryFixed Fixed.LagrangeCoeffs3;
  Metadata.Operation.QueryFixed Fixed.LagrangeCoeffs4;
  Metadata.Operation.EnableEqualityFixed Fixed.LagrangeCoeffs5;
  Metadata.Operation.EnableEqualityFixed Fixed.LagrangeCoeffs6;
  Metadata.Operation.EnableEqualityFixed Fixed.LagrangeCoeffs7;
  Metadata.Operation.QueryFixed Fixed.QSinsemilla2_1;
  Metadata.Operation.QueryLookup Lookup.TableX;
  Metadata.Operation.QueryLookup Lookup.TableY;
  Metadata.Operation.QueryFixed Fixed.QSinsemilla2_2
].

Definition operations : list (Metadata.Operation.t columns) :=
  allocation_operations ++
  [Metadata.Operation.EnableEqualityInstance Instance_.Primary] ++
  List.map Metadata.Operation.EnableEqualityAdvice Advice.all ++
  [Metadata.Operation.EnableConstant Fixed.LagrangeCoeffs0] ++
  rotated_advice_queries ++
  fixed_query_operations.

Definition state : Metadata.State.t :=
  Metadata.run indices operations Metadata.State.empty.

End OrchardConfigureMetadata.
