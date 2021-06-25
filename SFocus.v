
Require Import String. Import StringSyntax.       
From Ling Require Import BS. 
Import Ling.

(* Is this relevant? *)   

Add LoadPath  "/local/res/josh/coq" as Ling.

(* First compile BS.v as follows.
 /Applications/CoqIDE_8.13.1.app/Contents/Resources/bin/coqc -Q . Ling -vos BS.v

Josh has put in changes from BSm.v.
*)



(* muddy, copulatives *)

Definition muddy : AP := ET "muddy".
Definition is : (DP \ S) / AP := fun x y => x y.
 

(* Generalized bind *)
Definition gbind {a b c : Cat} (x : a || b -- c) : a || (c >> b) -- c :=
  fun k => x (fun e => k e e).

(* This is going to be thhe type of a structured antecedent. *)

Notation "x [ y ]" := (Focus y x) (at level 30, format "x [ y ]").

Definition bought := mkTV "bought".
Definition lunch : DP := Ec "lunch".
Definition alice : DP := Ec "alice".
(* Definition focus (x : DP) : DP[DP] := (x, id). *)
Definition focus {a : Cat} (x : a) : a[a] := (x, id).


Definition fextract {a b c d : Cat} (x : a || b -- (c[d])) : a || b -- c := fmap (fun (s : c[d]) => (snd s) (fst s)) x.

Definition fappf {a b c : Cat} (y : a / b) (x : b[c]) : a[c] :=
  (fst x, fun a => y (snd x a)).
Definition fappb {a b c : Cat} (x : b[c]) (y : b \ a) : a[c] := 
  (fst x, fun a => y (snd x a)).

Notation "x :f> y" := (fappf x y) (at level 40).
Notation "x <f: y" := (fappb x y) (at level 40).

Definition contrast {a} (f : S || S -- (S[a])) : (S[a] >> S) || S -- S := (fun k old => k (f (fun new => (snd new) (fst new) /\ (snd new) = (snd old) /\ (fst new) <> (fst old)))).

Definition ALICE_bought_lunch : S || (S[DP] >> S) -- S := 
    fextract (gbind (lift (focus alice <f: (bought :> lunch)))).

Definition JOHN_bought_lunch := 
    contrast (lift (focus john <f: (bought :> lunch))).


Check ALICE_bought_lunch.
Eval compute in ALICE_bought_lunch.
(*
     = fun k : Prop -> E * (E -> Prop) -> Prop =>
       k (EET "bought" (Ec "lunch") (Ec "alice"))
         (Ec "alice",
         fun a : E => EET "bought" (Ec "lunch") a)
     : 
S || S[DP] >> S
--
S
*)

Check bought :> lunch.
Check focus (bought :> lunch).
Check geach alice.
Check (geach alice) :f> (focus (bought :> lunch)).

Check fextract (gbind (lift ((geach alice) :f> (focus (bought :> lunch))))).

(*
Definition ALICE_bought_lunch : S || (S[DP] >> S) -- S := 
    fextract (gbind (lift (focus alice <f: (bought :> lunch)))).
*)

(* Structured VP-proposition antecedent. NB this does not have to do with focus. *)

Definition alice_BOUGHT_LUNCH : S || (S[DP \ S] >> S) -- S := 
    fextract (gbind (lift ((geach alice) :f> (focus (bought :> lunch))))). 

Check alice_BOUGHT_LUNCH. 
(*
S || S[DP \ S] >> S
--
S
*)

Eval compute in alice_BOUGHT_LUNCH.


(*
     = fun
         k : Prop ->
             (E -> Prop) * ((E -> Prop) -> Prop) -> Prop
       =>
       k (EET "bought" (Ec "lunch") (Ec "alice"))
         (EET "bought" (Ec "lunch"),               VP antecedent
         fun a : E -> Prop => a (Ec "alice"))      Abstract of the rest of the sentence.

(E -> Prop) * ((E -> Prop) -> Prop) is the type of the structured antecedent.  It's a pair of
a property and a proposition with a property hole.


The category of the structured binder is

S || S[DP \ S] >> S
--
S

indicating power to bind a S[DP \ S] pronoun. The category of [BEN did ---] should be

S[DP \ S] >> S || S
--
S

indicating a S[DP \ S] pronoun that is seeking an antecedent.

This is the type of [BEN is muddy] in the analysis from focus.v.  It indicates an unbound pronoun of 
propositional type.

lower (focus ben <| lift (is :> muddy))
     : 
(S >> S) || S
--
S

And this is the semantics.


fun (f : Prop -> Prop) (p : Prop) =>
       f (alt p (fun x : E => ET "muddy" x) (Ec "ben")) /\
       ET "muddy" (Ec "ben"
*)

(* Comment out stuff from older version.

Eval compute in (lower (ALICE_bought_lunch <| (lift and |> JOHN_bought_lunch))).


 How is this related to focus? 

Definition only {b : Cat} (x : b) : S || S -- (b).
  simpl.
  refine (fun k => k x /\ forall z, k z -> z = x).
Defined.

Eval compute in (lower (only john <| (lift (bought :> lunch)))). *)

(* Individuals *)
Definition ari : DP := Ec "ari".
Definition ben : DP := Ec "ben".

(* Copied from focus.v renaming focus to foc. *)

Parameter (alt : Prop -> ((interp DP) -> Prop) -> (interp DP) -> Prop).

Definition foc (x : DP) : ((S >> S) || S -- S)|| S -- DP :=
  fun k => (fun f => (fun p => (f (alt p k x)) /\ k x)).


(* Example with focus anaphora. This should be modified to parasitic focus-vp anaphora. *)

Check lower ((gbind (lift (ari <: (is :> muddy)))) <| 
      ((lift and) |> (lower ((foc ben)  <| (lift (is :> muddy)))))).


Eval compute in lower ((gbind (lift (ari <: (is :> muddy)))) <| 
      ((lift and) |> (lower ((foc ben)  <| (lift (is :> muddy)))))).

(* 
First conjunct of the focus example. It donates the antecedent using gbind. 

S || S >> S
--
S
*)

Check gbind (lift (ari <: (is :> muddy))) : S || S >> S -- S.
Check alice_BOUGHT_LUNCH.

(*
It is comparable to this, which binds S[DP\S] rather than S.
S || S[DP \ S] >> S
--
S

*)

(* The semantics for the first clauses compare as follows. The first function plugs in
the left conjunct proposition twice.

fun k : Prop -> Prop -> Prop =>
    k (ET "muddy" (Ec "ari"))
      (ET "muddy" (Ec "ari"))

The function for the structured antecedent ...

fun
  k : Prop ->                              Bound variable in position of left S.
      (E -> Prop) * ((E -> Prop) -> Prop)  Bound for a structured proposition.
          -> Prop
       =>
       k
         (EET "bought" (Ec "lunch")        Locally plug in the propistion 'alice bought lunch'
            (Ec "alice"))
         (EET "bought" (Ec "lunch"),       Distally plug in the structured proposition.
         fun a : E -> Prop => a (Ec "alice"))

*)

Eval compute in gbind (lift (ari <: (is :> muddy))) : S || S >> S -- S.

Eval compute in alice_BOUGHT_LUNCH.

(*
Look at the right conjunct for the focus case, to try to figure out what the right conjunct
for the ellipsis case should be.

(S >> S) || S
--
S

fun (f : Prop -> Prop)  Rest of the tree, with an argument for the local proposition position.
    (p : Prop)          Antecedent proposition.
    => f
         (alt p (fun x : E => ET "muddy" x)
            (Ec "ben")) /\
       ET "muddy" (Ec "ben")

Guess the semantics of BEN_F_did.

fun (f : Prop -> Prop)  Rest of the tree, maybe this is the same.
    (x : (E -> Prop) * ((E -> Prop) -> Prop)) antecedent structured proposition, it is a pair, use fst, snd.
    => f
         (alt ((snd x) (fst x)) (fun y : E => (fst x) y)
            (Ec "ben")) /\
       (fst x) (Ec "ben")
*) 

Check lower ((foc ben)  <| (lift (is :> muddy))). 
Eval compute in lower ((foc ben)  <| (lift (is :> muddy))).

Definition BEN_F_is_muddy : ((S >> S) || S -- S) := lower ((foc (ben : DP))  <| (lift (is :> muddy))).

Check BEN_F_is_muddy.

Definition BEN_F_did : ((S[DP \ S] >> S) || S -- S) :=
      fun (f : Prop -> Prop)   
      (x : (E -> Prop) * ((E -> Prop) -> Prop))  
    => f
         (alt ((snd x) (fst x)) (fun y : E => (fst x) y)
            (Ec "ben")) /\
       (fst x) (Ec "ben").

Check BEN_F_did.
(*
(S[DP \ S] >> S) || S
--
S
*)

Eval compute in alice_BOUGHT_LUNCH.
Check lower ((alice_BOUGHT_LUNCH <| ((lift and) |> BEN_F_did))).

Eval compute in lower ((alice_BOUGHT_LUNCH <| ((lift and) |> BEN_F_did))).

(*
(EET "bought" (Ec "lunch") (Ec "alice") /\
        alt
          (EET "bought" (Ec "lunch")
             (Ec "alice"))
          (fun y : E =>
           EET "bought" (Ec "lunch") y)
          (Ec "ben")) /\
       EET "bought" (Ec "lunch") (Ec "ben")
     : S
This looks good.
The conjunct in the middle is the focus presupposition.

*)


