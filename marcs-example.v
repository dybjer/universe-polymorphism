
Print sigT.

(* sigT (A : Type@{sigT.u0})
         (P : forall _ : A, Type@{sigT.u1}) :
    Type@{max(sigT.u0,sigT.u1)} *)

Print eq.

(* eq (A : Type@{eq.u0}) (x : A) : forall _ : A, Prop *)

Polymorphic Definition foo :=
   (fun X:Type =>  X = @sigT Type (fun Y : Type => Y -> X)).

Print foo.

(* foo@{u u0 u1} = fun X : Type@{u} => X = {Y : Type@{u0} & Y -> X}
      : Type@{u} -> Prop *)

(* u u0 u1 |= u < eq.u0
               u1 < sigT.u0
               u1 < u
               u <= sigT.u1
               u1 <= sigT.u1
               u0 = u1 *)

(* I don't understand u1, perhaps an auxiliary level, but we have u1 =
u0.
When I simply replace u1 by u0, here is what I understand, leaving out
"Type@":

       u < eq.u0 because X:u and we have =_u, that is, (eq u), with u:
eq.u0

       u0 < sigT.u0 because Y:u0 and we have (sigT u0) with u0: sigT.u0

       u0 < u because both sides of = should have the same type

       u <= sigT.u1 and u0 <= sigT.u1 because of Y->X with max(u,u0) <=
sigT.u1

There are no levels for Prop since Prop in Coq is impredicative.

*)
