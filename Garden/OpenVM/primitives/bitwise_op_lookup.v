Require Import Garden.Plonky3.M.
Require Import Garden.Plonky3.MExpr.

(*
pub struct BitwiseOperationLookupBusInteraction<T> {
    pub x: T,
    pub y: T,
    pub z: T,
    pub op: T,
    pub bus: LookupBus,
    is_lookup: bool,
}
*)
Module BitwiseOperationLookupBusInteraction.
  Record t {T : Set} : Set := {
    x : T;
    y : T;
    z : T;
    op : T;
    bus : LookupBus.t;
    is_lookup : bool;
  }.
  Arguments t : clear implicits.
End BitwiseOperationLookupBusInteraction.

Module Impl_BitwiseOperationLookupBusInteraction.
  (*
    pub fn eval<AB>(self, builder: &mut AB, count: impl Into<AB::Expr>)
    where
        AB: InteractionBuilder<Expr = T>,
    {
        let key = [self.x, self.y, self.z, self.op];
        if self.is_lookup {
            self.bus.lookup_key(builder, key, count);
        } else {
            self.bus.add_key_with_lookups(builder, key, count);
        }
    }
  *)
  Definition eval
    (self : BitwiseOperationLookupBusInteraction.t Expr.t)
    (count : Expr.t) :
    MExpr.t unit :=
  let key := [
    self.(BitwiseOperationLookupBusInteraction.x);
    self.(BitwiseOperationLookupBusInteraction.y);
    self.(BitwiseOperationLookupBusInteraction.z);
    self.(BitwiseOperationLookupBusInteraction.op)
  ] in
  if self.(BitwiseOperationLookupBusInteraction.is_lookup) then
    Impl_LookupBus.lookup_key self.(BitwiseOperationLookupBusInteraction.bus) key count
  else
    Impl_LookupBus.add_key_with_lookups self.(BitwiseOperationLookupBusInteraction.bus) key count.
End Impl_BitwiseOperationLookupBusInteraction.

(*
pub struct BitwiseOperationLookupBus {
    pub inner: LookupBus,
}
*)
Module BitwiseOperationLookupBus.
  Record t : Set := {
    inner : LookupBus.t;
  }.
End BitwiseOperationLookupBus.

(* impl BitwiseOperationLookupBus { *)
Module Impl_BitwiseOperationLookupBus.
  (*
    pub fn push<T>(
        &self,
        x: impl Into<T>,
        y: impl Into<T>,
        z: impl Into<T>,
        op: impl Into<T>,
        is_lookup: bool,
    ) -> BitwiseOperationLookupBusInteraction<T> {
        BitwiseOperationLookupBusInteraction {
            x: x.into(),
            y: y.into(),
            z: z.into(),
            op: op.into(),
            bus: self.inner,
            is_lookup,
        }
    }
  *)
  Definition push
    (self : BitwiseOperationLookupBus.t)
    (x y z op : Expr.t)
    (is_lookup : bool) :
    BitwiseOperationLookupBusInteraction.t Expr.t :=
  {|
    BitwiseOperationLookupBusInteraction.x := x;
    BitwiseOperationLookupBusInteraction.y := y;
    BitwiseOperationLookupBusInteraction.z := z;
    BitwiseOperationLookupBusInteraction.op := op;
    BitwiseOperationLookupBusInteraction.bus := self.(BitwiseOperationLookupBus.inner);
    BitwiseOperationLookupBusInteraction.is_lookup := is_lookup;
  |}.

  (*
    pub fn send_range<T>(
        &self,
        x: impl Into<T>,
        y: impl Into<T>,
    ) -> BitwiseOperationLookupBusInteraction<T>
    where
        T: FieldAlgebra,
    {
        self.push(x, y, T::ZERO, T::ZERO, true)
    }
  *)
  Definition send_range
    (self : BitwiseOperationLookupBus.t)
    (x y : Expr.t) :
    BitwiseOperationLookupBusInteraction.t Expr.t :=
  Impl_BitwiseOperationLookupBus.push self x y Expr.ZERO Expr.ZERO true.
End Impl_BitwiseOperationLookupBus.
