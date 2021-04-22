Require Import String. Import StringSyntax.

Module Ling. 

  Parameter (E : Type).
  Parameter (Ec : string -> E).
  Parameter (EET : string -> E -> E -> Prop).
  Parameter (ET : string -> E -> Prop).
  Parameter (baseAdj : string -> E -> Prop).
  Parameter (Wants : Prop -> E -> Prop).
  Parameter (Knows : Prop -> E -> Prop).
  Parameter (know : E -> Prop -> Prop).
  Parameter (Mother : E -> E).      

  (* Syntactic categories. *)
  Inductive Cat :=
  | DP | S | AP
  | ArrL : Cat -> Cat -> Cat
  | ArrR : Cat -> Cat -> Cat
  | Bound : Cat -> Cat -> Cat
  | GapL : Cat -> Cat -> Cat
  | GapR : Cat -> Cat -> Cat
  | Tow : Cat -> Cat -> Cat -> Cat.

  (* Mapping of syntactic categories to semantic types. *)
  Fixpoint interp (c : Cat) : Type :=
    match c with
    | DP => E
    | S => Prop
    | AP => E -> Prop
    | ArrL c1 c2 => interp c1 -> interp c2             
    | ArrR c1 c2 => interp c2 -> interp c1
    | GapL a b => interp a -> interp b
    | GapR a b => interp b -> interp a
    | Bound x y => interp x -> interp y
    | Tow a b c => (interp c -> interp b) -> interp a
                                                    end.

  (* This lets me write x : c, where x is a lambda term and c is a category. *)
   Coercion interp : Cat >-> Sortclass.

Notation "x \ y" := (ArrL x y) (at level 40).
Notation "x / y" := (ArrR x y).
Notation "x >> y" := (Bound x y) (at level 40).
Notation "x \\ y" := (GapL x y) (at level 40).
Notation "x // y" := (GapL x y) (at level 40).

Notation "x || y -- z" := (Tow x y z) (at level 30, format "'//' x  ||  y '//' -- '//' z").

Definition john : DP := (Ec "john").

(* Lift is like the monadic return. *) 
(* c is local type, a is scope type. *)
Definition lift {a : Cat} {c : Cat} (x : c) : a || a -- c :=
  (fun k => k x).

(* In (b || a -- c), c is the local type, a is the scope,
   and b is the scope result. *)

(* Forward Geach type raising.
  NB this uses Bar-Hillel notation for leftward slashes. *)
Definition geach {a : Cat} {c : Cat} (x : c) : (a / (c \ a)) :=
  (fun k => k x).

(* Forward and backward application, with the order of arguments
  following the surface order. *)
Definition appf {a b: Cat} (y : (a / b)) (x : b) : a :=
  (y x).

Definition appb {a b: Cat} (x : b) (y : (b \ a)) : a :=
  (y x).


(* Collapse tower at S. The result is the scope result b. *) 
Definition lower {a : Cat} (x : a || S -- S) : a := x id.

(* Apply locally, and compose at the continuation level.
  The order of arguments is the surface order. *)
Definition cleft {a b c x y : Cat}
           (f : a || b -- x)
           (g : b || c -- (x \ y)) : a || c -- y :=
  (fun k => f (fun x => g (fun y => k (y x)))).

Definition cright {a b c x y : Cat} 
          (f : a || b -- (x / y)) 
          (g : b || c -- y) : a || c -- x :=
    (fun k => f (fun x => g (fun y => k (x y)))). 


(* Swap the notation from Josh, to match notation in categorial
   grammar, e.g. Steedman. Now the arrow points at the argument. *)
Notation "x <| y" := (cleft x y) (at level 41).
Notation "x |> y" := (cright x y) (at level 41).

Definition TV := (DP \ S) / DP.

Definition mkTV (s : string) : TV := EET s.
Definition mary : DP := (Ec "mary").

(* This puts the subject first in the atomic formula (love john mary) *)
Definition loves : TV := fun (y : E) (x : E) => ((mkTV "love") x y).

(* Basic application. *)   

Notation "x :> y" := (appf x y) (at level 40).
Notation "x <: y" := (appb x y) (at level 40).

Check loves :> mary.
Check john <: (loves :> mary).
Eval compute in (john <: (loves :> mary)).

Check (geach john). 
Check (geach john) : S / (DP \ S).
Eval compute in ((geach john) : S / (DP \ S)).

Check (geach john) :> (loves :> mary).
Eval compute in ((geach john) :> (loves :> mary)).


(* Continuation quantifiers. *)

Definition everyone : S || S -- DP := fun (k : E -> Prop) =>
                                        forall x, ET "person" x -> k x.

Definition someone : S || S -- DP := fun k => exists x, ET "person" x /\ k x. 


Definition to_leave : (DP \ S) := (ET "leave" : DP \ S).

Definition wants : ((DP \ S) / S) := (Wants : (DP \ S) / S).



(* Syntax of quantifiers with default scopes. The transitive verb is
   lifted to a tower in order to combine. *)
 
Check (everyone <| (lift loves |> someone)). 
Check (someone <| (lift loves |> everyone)). 


(* Simple quantifier scope. *)

Eval compute in (lower (everyone <| lift to_leave)).

Check (lift loves) |> someone.
Check everyone <| ((lift loves) |> someone).

(* The scopes come out in linear order. *)

Eval compute in (lower (everyone <| ((lift loves) |> someone))).


(* This one has a variable scope type, which is also the scope
   result type. *)
 
Check (lift john). 

(* This restricts it. *)

Check (lift john) : S || S -- DP.
Eval compute in ((lift john) : S || S -- DP).


(* Section 1.9 in Barker & Shan *)

(* This has matrix scope for the quantifier. *) 

Eval compute in (
                 lower (lift mary <| (lift wants |>
                                           (everyone <| lift to_leave)))).
(* "(lift (lower" unscopes the quantifier. *)

Eval compute in (lower (lift mary <| (lift wants |>
                                           (lift (lower (everyone <| lift to_leave)))))).

(* This is equivalent to the above, without tower in the higher part of the derivation. *)

Eval compute in (mary <: (wants :> (lower (everyone <| lift to_leave)))).


(***  Binding  ***)

(* The operator bind applies to a quantifier that takes scope at b,
  and creates one that takes scope at DP >> b).
  The latter is a phrase where a pronoun such as 'he' has just been bound. *)

Definition bind {a b : Cat}
  (x : a || b -- DP) :
  a || (DP >> b) -- DP :=
  fun k => x (fun e => k e e).


(* Local DP that takes scope at S to give DP >> S, which binds
   variable in the position of the pronoun. *)

Definition he : (DP >> S) || S -- DP := fun k => k.

(* Beginning of Chapter 2 in Barker & Shan, listing (28) *)
Eval compute in (lower (he <| lift to_leave)).

Definition mother : (DP \ DP) := (Mother : DP \ DP).


(* Listing 31 *)
(* Everyone loves his mother *)
Eval compute in (lower (
                     bind everyone <|
                     (lift loves |> (he <| lift mother)))).


(* Listing 44, from Chapter 3 *)
(* Someone entered. He left *)
Definition and : (S \ S) / S := fun p2 p1 => p1 /\ p2.

Definition entered : DP \ S := ET "enter".
Definition left : DP \ S := ET "left".

Eval compute in (lower (
                     (bind someone <| lift entered)
                       <|
                       (lift and |>
                             (he <| lift left))
                             
                )).




(***** Multi-level towers for scope ambiguity ******)
Definition cleft2 {E F H C D G A B : Cat}
           (l : E || F -- (C || D -- A))
           (r : F || H -- (D || G -- (A \ B))) :
           E || H -- (C || G -- B).
  unfold interp in *; simpl in *.
  firstorder.
Defined.

Definition cright2 {E F H C D G A B : Cat}
           (l : E || F -- (C || D -- (A / B)))
           (r : F || H -- (D || G -- (B))) :
           E || H -- (C || G -- A).
  unfold interp in *; simpl in *.
  firstorder.
Defined.

Definition fmap {a b c d : Cat} (f : c -> d) : a || b -- c -> a || b -- d.
  intros x k.
  apply x; intro hc.
  apply k.
  apply f.
  apply hc.
Defined.


(* Listing 52, chapter 4 of Barker & Shan *)

(* Ambiguous notation resolved by types? 
Notation "x <|> y" := (cleft2 x y) (at level 41).
Notation "x <|> y" := (cright2 x y) (at level 41). *)

Notation "x ||> y" := (cright2 x y) (at level 41).

Notation "x <|| y" := (cleft2 x y) (at level 41).

Eval compute in (lift someone).


(* Discussion around listing (54) *)
(* lift2 lifts a tower, e.g. quantifier, to a double tower. *)

Definition lift2 {s a b c : Cat} (x : a || b -- c) : a || b -- (s || s -- c) :=
  fmap lift x.

Definition lower2 {a b c : Cat} (x : a || b -- (c || S -- S)) : a || b -- c :=
  fmap lower x.

(* Inverse scope by doing alternative lift / lowers *)
(* Listing (55) *)
Check (lower (lower2 (lift someone <|| ((lift (lift loves)) ||> lift2 everyone)))).
Eval compute in (lower (lower2 (lift someone <|| ((lift (lift loves)) ||> lift2 everyone)))).

End Ling.


