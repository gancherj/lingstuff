Require Import String. Import StringSyntax.

Module Ling. 

  Parameter (E : Type).
  Parameter (baseE : string -> E).
  Parameter (baseVP : string -> E -> E -> Prop).
  Parameter (baseVP_intr : string -> E -> Prop).
  Parameter (baseAdj : string -> E -> Prop).
  Parameter (Wants : Prop -> E -> Prop).
  Parameter (Knows : Prop -> E -> Prop).
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
Notation "x // y" := (GapR x y) (at level 40).

Notation "x || y -- z" := (Tow x y z) (at level 30, format "'//' x  ||  y '//' -- '//' z").


Definition john : DP := (baseE "john").

(* Lift is like the monadic return. *)
Definition lift {a : Cat} {c : Cat} (x : c) : a || a -- c :=
  (fun k => k x).

Definition lower {a : Cat} (x : a || S -- S) : a := x id.

Definition cleft {a b c x y : Cat}
           (f : a || b -- x)
           (g : b || c -- (x \ y)) : a || c -- y :=
  (fun k => f (fun x => g (fun y => k (y x)))).

Definition cright {a b c x y : Cat} (f : a || b -- (x / y)) (g : b || c -- y) : a || c -- x :=
    (fun k => f (fun x => g (fun y => k (x y)))).

Notation "x |> y" := (cleft x y) (at level 41).
Notation "x <| y" := (cright x y) (at level 41).

Definition VP := (DP \ S) / DP.

Definition mkVP (s : string) : VP := baseVP s.
Definition loves : VP := (mkVP "loves").
Definition mary : DP := (baseE "mary").

Definition everyone : S || S -- DP := fun (k : E -> Prop) =>
                                        forall x, k x.

Definition someone : S || S -- DP := fun k => exists x, k x.

Check (everyone |> (lift loves <| someone)).
Check (someone |> (lift loves <| everyone)).


Definition to_leave : (DP \ S) := (baseVP_intr "leave" : DP \ S).

Definition wants : ((DP \ S) / S) := (Wants : (DP \ S) / S).

(* Section 1.9 in Barker & Shan *)

Eval compute in (
                 lower (lift mary |> (lift wants <|
                                           (everyone |> lift to_leave)))).

Eval compute in (lower (lift mary |> (lift wants <|
                                           (lift (lower (everyone |> lift to_leave)))))).


(***  Binding  ***)

Definition bind {a b : Cat}
  (x : a || b -- DP) :
  a || (DP >> b) -- DP :=
  fun k => x (fun e => k e e).


Definition he : (DP >> S) || S -- DP := fun k => k.

(* Beginning of Chapter 2 in Barker & Shan, listing (28) *)
Eval compute in (lower (he |> lift to_leave)).

Definition mother : (DP \ DP) := (Mother : DP \ DP).


(* Listing 31 *)
(* Everyone loves his mother *)
Eval compute in (lower (
                     bind everyone |>
                     (lift loves <| (he |> lift mother)))).


(* Listing 44, from Chapter 3 *)
(* Someone entered. He left *)
Definition and : (S \ S) / S := fun p1 p2 => p1 /\ p2.

Definition entered : DP \ S := baseVP_intr "enter".
Definition left : DP \ S := baseVP_intr "left".

Eval compute in (lower (
                     (bind someone |> lift entered)
                       |>
                       (lift and <|
                             (he |> lift left))
                             
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
Notation "x |>> y" := (cleft2 x y) (at level 41).
Notation "x <<| y" := (cright2 x y) (at level 41).

Eval compute in (lift someone).


(* Discussion around listing (54) *)
Definition lift2 {s a b c : Cat} (x : a || b -- c) : a || b -- (s || s -- c) :=
  fmap lift x.

Definition lower2 {a b c : Cat} (x : a || b -- (c || S -- S)) : a || b -- c :=
  fmap lower x.

(* Inverse scope by doing alternative lift / lowers *)
(* Listing (55) *)
Eval compute in (lower (lower2 (lift someone |>> ((lift (lift loves)) <<| lift2 everyone)))).

End Ling.


