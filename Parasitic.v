
Require Import String. Import StringSyntax.           
 
(* Is this relevant? *)   

Add LoadPath  "/local/res/josh/coq" as Ling.

(* First compile BS.v as follows.
 /Applications/CoqIDE_8.13.1.app/Contents/Resources/bin/coqc -Q . Ling -vos BSm2.v

Josh has put in changes from BSm.v.
*)


From Ling Require Import BSm2. 
Import Ling.

(* muddy, copulatives *)

Definition muddy : AP := et "muddy".
Definition is : (DP \ S) / AP := fun x y => x y.
 

(* Generalized bind *)
Definition gbind {a b c : Cat} (x : a || b -- c) : a || (c >> b) -- c :=
  fun k => x (fun y => k y y).

(* 
 This is the type of a structured antecedent. S[DP\S] encodes a propositional and
 a predicate antecedent.
*)

Notation "x [ y ]" := (Struct y x) (at level 30, format "x [ y ]").


(* The recursive focus stuff is cut. 

   
The category of the structured binder is

S || S[DP \ S] >> S
--
S

indicating power to bind a S[DP \ S] pronoun. The category of [BEN did ---] should be

S[DP \ S] >> S || S
--
S
  
*)

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
 
Guess the semantics of BEN_F_did.

  BEN_F_did equires a structured antecedent, providing a propositional and a VP
  antecedent.
*)

Definition BEN_F_did : ((S[DP \ S] >> S) || S -- S) :=
      fun (f : Prop -> Prop)   
      (x : (E -> Prop) * ((E -> Prop) -> Prop))  
    => f
         (alt ((snd x) (fst x)) (fun y : E => (fst x) y)
            ben) /\
       (fst x) ben.


(*
(S[DP \ S] >> S) || S
--
S
*) 

Definition ALICE_F_did : ((S[DP \ S] >> S) || S -- S) :=
      fun (f : Prop -> Prop)   
      (x : (E -> Prop) * ((E -> Prop) -> Prop))  
    => f
         (alt ((snd x) (fst x)) (fun y : E => (fst x) y)
            alice) /\
       (fst x) alice.

Check ALICE_F_did.


(* 
Define an operator that applies to VP to create the structured antecedent.
This has the two towers strategy, where the result for the lower tower
is a tower.
*)
 
(* TODO: generalize to DP \ DP \ S, .... *)

(* TODO: generalize ant to apply to a tower, not just DP \ S *)
(* allow ant to apply to not just S on the left, but like DP >> S *)

Definition ant (f : DP \ S) : (S || (S[DP \ S] >> S) -- S)|| S -- (DP \ S) :=
    fun c => (fun k =>
       k (c f)
         (f, fun a : E -> Prop => (c a))).

Eval compute in lower ((lift john) <| (ant (kissed ben))).
(*
fun k : Prop ->
             (E -> Prop) * ((E -> Prop) -> Prop) -> Prop
       =>
       k (eet "kiss" (e "john") (e "ben"))
         (fun x : E => eet "kiss" x (e "ben"),
         fun a : E -> Prop => a (e "john"))
     : 
S || S[DP \ S] >> S
--
S

*)

Definition john_kissed_ben_and_ALICE_F_did := 
 lower ((lower ((lift john) <| (ant (kissed ben)))) <| ((lift and) |> ALICE_F_did)). 

Eval compute in john_kissed_ben_and_ALICE_F_did.

(*
     = (eet "kiss" (e "john") (e "ben") /\
        alt (eet "kiss" (e "john") (e "ben"))
          (fun y : E => eet "kiss" y (e "ben"))
          (e "alice")) /\
       eet "kiss" (e "alice") (e "ben")
     : S


In the above, ALICE_F_did is a primitive, rather than being derived compositionally. Fixing this is
the next step.

It should be done in a way that 'did' contributes a simple VP antecedent, or one with one or more pronouns.

*) 

Definition did : ((DP \ S) >> S) || S -- (DP \ S) := fun k => k.

(* FOC turns a structured anaphor into a regular one, adding the alt operator along the way. *)

Definition FOC (a : DP) : (S[DP \ S] >> S) || ((DP \ S) >> S) -- DP :=
  fun (k : DP -> (DP \ S) >> S)
      (ana : S[DP \ S]) =>
    k a (fst ana) /\
    alt ((snd ana) (fst ana)) (fun y => (fst ana) y) a.

Check (FOC alice <| did).
Definition compositional_version' := lower ((lower ((lift john) <| (ant (kissed ben)))) <| ((lift and) |> (FOC alice <| did))). 

Eval compute in compositional_version'.

Goal john_kissed_ben_and_ALICE_F_did <-> compositional_version'.
  firstorder.
Qed.

(* TODO's:

   - Generalize to other variable versions, 
       NP:
       "A short man ate ice cream, and a TALL one did as well."

       no variables:
       "John praised his mother, and BEN praised his mother too."

   - Enforce only structured anaphors:
      - maybe disallow BIND on (DP \ S)? And only allow structured anaphoric bind
      - block plain VP anaphors across S's
           - Maybe add a typeclass constraint on cleft/cright (|> / <|) that blocks this propogation

   - Do covariance / sloppy identity in this framework
      - covariance:
        ARI knows he is muddy, but ben doesn't know this.
        -> ben doesn't know ben is muddy
        -> ben doesn't know ari is muddy

*)
