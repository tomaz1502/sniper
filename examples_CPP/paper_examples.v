(**********************************************************************)
(* This file linearly presents the examples of the submission to      *)
(*   CPP'23, in order to be followed along with the paper.            *)
(**********************************************************************)


From Sniper Require Import Sniper.
From SMTCoq Require SMTCoq.
Require Import ZArith Psatz.
From Trakt Require Trakt.
From Hammer Require Hammer.
From mathcomp Require all_ssreflect all_algebra.
From mathcomp.zify Require ssrZ zify_algebra.
Require Cdcl.NOlia.
Import ListNotations.
From Coq Require ZifyClasses ZifyBool ZifyInst.


(* We start with the small illustrating examples. *)
Module small_examples.
Import Trakt.
Import Hammer.


(* Both SMTCoq and itauto provide a tactic named `smt`. We introduce
   notations to prevent the confusion. *)
Tactic Notation "smt_SMTCoq" := smt.
Tactic Notation "smt_itauto" := Cdcl.NOlia.smt.


(* Examples from Section 2 *)

(* An example completely automatized by the hammer tactic *)
Lemma length_rev_app : forall B (l l' : list B),
length (rev (l ++ l')) = length l + length l'.
Proof. scongruence use: app_length, rev_length. Qed.

(* A variant that hammer cannot solve because it lacks arithmetical
   features *)
Lemma length_rev_app_cons :
forall B (l l' : list B) (b : B),
length (rev (l ++ (b::l'))) =
(length l) + (length l') + 1.
Proof. (* Fail hammer. *) Fail scongruence use: app_length, rev_length.
Abort.

(* sauto and SMTCoq cannot perform case analysis in general *)
Lemma app_nil_rev B (l l' : list B) (a : B) : (rev l) ++ l' = nil -> l = [] \/ l' = [].
Proof. Fail sauto dep: on. Fail smt_SMTCoq. Fail verit.
Abort.

(* SMTCoq can solve goals about aritmetic... *)
Lemma eZ : forall (z : Z), (z >= 0 -> z < 1 -> z = 0)%Z.
Proof. smt_SMTCoq. Qed.

Module Int.

Import all_ssreflect all_algebra.

(* ... but only on type Z. *)
Lemma eint : forall (z : int), (z >= 0 -> z < 1 -> z = 0)%R.
Proof. Fail smt_SMTCoq. Abort.

(* Thanks to zify, lia can prove goals about configured types of integers... *)
Lemma eint : forall (z : int), (z >= 0 -> z < 1 -> z = 0)%R.
Proof. lia. Qed.

(* ... but not in the presence of symbols oustide arithmetic, such as _::_ *)
Lemma congr_int : forall (z : int), ((z + 1) :: nil = (1 + z) :: nil)%R.
Proof. Fail lia. Abort.

(* itauto's smt tactic is able to solve this goal... *)
Lemma eintb : forall (z : int), (z + 1 == 1 + z)%R = true.
Proof. smt_itauto. Abort.

(* ... but it fails on this one because of the uninterpreted function f *)
Lemma eintcb : forall (f : int -> int) (z : int),
(f (z + 1) == f (1 + z))%R = true.
Proof. Fail smt_itauto. Abort.

End Int.


(* Examples from Section 3 *)
(* 3.2  Axiomatizing inductive types *)

(* Inversion principle of inductive relations *)
Inductive add : nat -> nat -> nat -> Prop :=
| add0 : forall n, add 0 n n
| addS : forall n m k, add n m k -> add (S n) m (S k).

Goal forall x y r, add x y r -> add y x r.
Proof.
  (* This tactic automatically scans the goal to add all relevent
     inversion principles *)
  inv_principle_all.
Abort.

(* Interpretation of algebraic datatypes & Generation statement for inductive types *)
Goal forall (A:Type) (l1 l2:list A), rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros A l1 l2.
  (* This tactic automatically scans the goal to add all relevent lemmas
     stating that constructeurs are injective and pairwise disjoint. The
     tactic is parameterizd by a tuple of algebraic types not to be
     detailed (unit if not needed). *)
  interp_alg_types_context_goal unit.
  (* This tactic automatically states that the elements of a given
     algebraic datatype are generated by its constructors *)
  get_projs_in_variables list.
Abort.

(* Elimination of pattern matching *)
Goal (forall A d l n, @nth_default A d l n =
                        match nth_error l n with
                        | Some x => x
                        | None => d
                        end) -> nth_default 0%Z nil 42%nat = 0%Z.
Proof.
  intro H1.
  (* This tactic eliminates (possibly dependent) pattern matching in a
     given hypothesis *)
  eliminate_dependent_pattern_matching H1.
Abort.

(* 3.3  Going first order *)

(* Higher-order equalities *)
Goal forall (A:Type) (f g:A -> A -> A), f = g -> forall x, f (g x x) x = g (f x x) x.
Proof.
  intros A f g H.
  (* This tactic deduces first-order equalities from higher-order ones *)
  expand_hyp H.
Abort.

(* Monomorphization *)

(* We have two versions of the tactic: one generates instances for all
types appearing in the context, and the other generates fewer instances
by looking at applications of polymorphic inductive types. *)
Tactic Notation "inst_with_subterms_of_type_type" := inst.
Tactic Notation "inst_with_chosen_parameters" := elimination_polymorphism.

Goal (forall (A B : Type) (x1 x2 : A) (y1 y2 : B),
         (x1, y1) = (x2, y2) -> x1 = x2 /\ y1 = y2) ->
     forall (x1 x2 : option Z) (y1 y2 : list unit),
       (x1, y1) = (x2, y2) -> x1 = x2 /\ y1 = y2.
Proof.
  intro H. inst_with_subterms_of_type_type. (* 25 instances *)
  Undo. inst_with_chosen_parameters. (* 1 instance *)
Abort.

(* 3.4  Giving meaning to symbols *)

(* Expanding constants *)
Goal forall l u x y, in_int l u x -> in_int l x y -> in_int l u y.
Proof.
  (* This tactic adds a lemma expanding the body of the definition *)
  get_def in_int.
Abort.

(* Anonymous fixpoints *)
Goal forall (A:Type) (l1 l2:list A), rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros A l1 l2.
  (* When expanding the definition of rev... *)
  get_def rev.
  (* ... we get a higher-order equality... *)
  expand_hyp rev_def.
  (* ... with an anonymous fixpoint, that can be eliminated thanks to
     this tactic. *)
  eliminate_fix_hyp H.
Abort.

(* 3.4.2  Theories *)

(* Example 3.3: Trakt's translation from a predicate on int into a
   predicate on Z *)

(* We add embeddings between Z and int to Trakt's database... *)
Import all_ssreflect all_algebra.
Import ZifyClasses ZifyBool ZifyInst ssrZ zify_algebra AlgebraZifyInstances.

Notation Z_to_int := ssrZ.int_of_Z.

Lemma int_Z_gof_id : forall (x : int), x = Z_to_int (Z_of_int x).
Proof. intro x. symmetry. exact (Z_of_intK x). Qed.

Lemma int_Z_fog_id : forall (z : Z), Z_of_int (Z_to_int z) = z.
Proof. intro x. exact (ssrZ.int_of_ZK x). Qed.

Trakt Add Embedding int Z Z_of_int Z_to_int int_Z_gof_id int_Z_fog_id.

Lemma eqint_eqZ_equiv : forall (x y : int), x = y <-> Z_of_int x = Z_of_int y.
Proof. apply (@TRInj _ _ _ _ Op_int_eq). Qed.

Trakt Add Relation 2 (@eq int) (@eq Z) eqint_eqZ_equiv.
Trakt Add Conversion GRing.Zmodule.sort.

(* ... which allows Trakt to actually go from int to Z *)
Lemma trakt_Z_predicate :  forall (P : int -> Prop) (x : int), P x <-> P x.
Proof. intros P x. trakt Z Prop. Abort.

(* Example 3.4: Trakt's translation can also map the signaturs of theories *)

(* We add equivalences between + and 0 of int and Z... *)

Local Delimit Scope Z_scope with Z.

Lemma add_embedding_property : forall (x y : int),
  Z_of_int (x + y) = (Z_of_int x + Z_of_int y)%Z.
Proof. apply (@TBOpInj _ _ _ _ _ _ _ _ _ _ Op_addz). Qed.

Lemma zero_embedding_property : Z_of_int 0 = 0%Z. Proof. reflexivity. Qed.

Trakt Add Symbol intZmod.addz Z.add add_embedding_property.
Trakt Add Symbol (GRing.zero int_ZmodType) Z0 zero_embedding_property.
Trakt Add Conversion GRing.add.
Trakt Add Conversion GRing.zero.

(* ... so that Trakt can use them *)

Lemma trakt_int_Z_Prop :
  forall (f : int -> int -> int) (x y : int),
    f x (y + 0)%R = f (x + 0)%R y.
Proof. trakt Z Prop. Abort.


(* Example 3.3: Trakt's translation can target Boolean logic *)

(* We add equivalence between propositional and Boolean equality... *)

Lemma eq_int_equivalence_property :
  forall (x y : int), x = y <-> (Z_of_int x =? Z_of_int y)%Z = true.
Proof.
  intros x y.
  refine (iff_trans (eqint_eqZ_equiv x y) _).
  symmetry.
  apply Z.eqb_eq.
Qed.

Trakt Add Relation 2
  (@eq (GRing.Zmodule.sort int_ZmodType)) Z.eqb eq_int_equivalence_property.

(* ... which allows Trakt to go towards Boolean logic *)

Lemma trakt_int_Z_bool :
  forall (f : int -> int) (x : int), (f x + 0 = f x)%R.
Proof. trakt Z bool. Abort.


(* Example 3.4: Trakt's translation can deal with partial embeddings *)

(* Let us now embed nat, its symbols and relations into Z... *)

Lemma nat_Z_gof_id : forall (n : nat), n = Z.to_nat (Z.of_nat n).
Proof. symmetry. apply Nat2Z.id. Qed.

Lemma pC_nat : forall (n : nat), (0 <= Z.of_nat n)%Z.
Proof. apply Nat2Z.is_nonneg. Qed.

Lemma id2C_nat : forall (z : Z), (0 <= z)%Z -> Z.of_nat (Z.to_nat z) = z.
Proof. apply Z2Nat.id. Qed.

Trakt Add Embedding nat Z Z.of_nat Z.to_nat nat_Z_gof_id id2C_nat pC_nat.

Lemma eqnat_eqZ_equiv : forall (n m:nat), n = m <-> Z.of_nat n = Z.of_nat m.
Proof. symmetry. apply Nat2Z.inj_iff. Qed.

Trakt Add Relation 2 (@eq nat) (@eq Z) eqnat_eqZ_equiv.

Lemma Natadd_Zadd_embed_eq : forall (n m : nat),
  Z.of_nat (n + m) = (Z.of_nat n + Z.of_nat m)%Z.
Proof.
  apply Nat2Z.inj_add.
Qed.

Trakt Add Symbol addn Z.add Natadd_Zadd_embed_eq.

(* ... so that Trakt can also deal wit it *)

Lemma trakt_nat_Z_Prop : forall (f : nat -> nat) (n : nat), (f n + 0 = f n)%nat.
Proof. trakt Z Prop. Abort.


(* Examples from Section 4 *)
(* 4.1  Single-component pre-processing *)

(* Example 4.1: Pre-processing for itauto *)

(* We add multiplication and comparison to the database of Trakt... *)

Lemma mulz_Zmul_embed_eq : forall (x y : int),
  Z_of_int (intRing.mulz x y) = (Z_of_int x * Z_of_int y)%Z.
Proof. apply (@TBOpInj _ _ _ _ _ _ _ _ _ _ Op_mulz). Qed.

Trakt Add Symbol intRing.mulz Z.mul mulz_Zmul_embed_eq.
Trakt Add Conversion GRing.mul.

Definition Order_le_int_Prop : int -> int -> Prop := fun x y => (x <= y)%R = true.

Lemma Order_le_int_bool_Prop (x y:int) : (x <= y)%R = true <-> Order_le_int_Prop x y.
Proof. reflexivity. Qed.

Trakt Add Relation 2
  (@Order.le ring_display int_porderType)
  Order_le_int_Prop
  Order_le_int_bool_Prop.

Lemma Orderle_int_Zle_equiv (x y : int) :
  Order_le_int_Prop x y <-> (Z_of_int x <= Z_of_int y)%Z.
Proof.
  unfold Order_le_int_Prop.
  assert (H: (x <= y)%R = (Z_of_int x <=? Z_of_int y)%Z)
    by apply (@TBOpInj _ _ _ _ _ _ _ _ _ _ Op_int_le).
  now rewrite H Z.leb_le.
Qed.

Trakt Add Relation 2
  Order_le_int_Prop
  Z.le
  Orderle_int_Zle_equiv.

Lemma int_2 : Z_of_int (2%:Z)%R = 2%Z.
Proof. reflexivity. Qed.

Trakt Add Symbol ((2%:Z)%R) (2%Z) int_2.

(* ... in order to fully pre-process this goal *)

Goal forall (f : int -> int) (x : int),
    (f (2%:Z * x) <= f (x + x))%R = true.
Proof. Fail smt_itauto. trakt Z Prop. smt_itauto. Qed.

(* Example 4.2: Pre-processing for itauto *)
(* Everything is already in the database of Trakt *)
Goal forall (f : int -> int) (x : int), (f x + 0)%R = f x.
Proof. trakt Z Prop. smt_itauto. Qed.

(* Example 4.3: Pre-processing for firstorder congruence *)
Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Theorem SSSSev_ev : forall (n : nat),
ev (S (S (S (S n)))) -> ev n.
Proof.
  Fail firstorder congruence.
  inv_principle_all; firstorder congruence.
Qed.

(* Example 4.4: Pre-processing for sauto (hammer) *)
Lemma app_eq_nil (A : Type) (l l' : list A):
  l ++ l' = [] -> l = [] /\ l' = [].
Proof.
  Fail sauto.
  get_gen_statement_for_variables_in_context; sauto.
Qed.

(* Example 4.5: Pre-processing for sauto (hammer), on a CompCert goal *)
 Inductive memory_chunk : Type :=
  | Mint8signed     (**r 8-bit signed integer *)
  | Mint8unsigned   (**r 8-bit unsigned integer *)
  | Mint16signed    (**r 16-bit signed integer *)
  | Mint16unsigned  (**r 16-bit unsigned integer *)
  | Mint32          (**r 32-bit integer, or pointer *)
  | Mint64          (**r 64-bit integer *)
  | Mfloat32        (**r 32-bit single-precision float *)
  | Mfloat64        (**r 64-bit double-precision float *)
  | Many32          (**r any value that fits in 32 bits *)
  | Many64.         (**r any value *)

Definition memory_chunk_to_Z mc :=
      match mc with
      | Mint8signed => 0%Z
      | Mint8unsigned => 1%Z
      | Mint16signed => 2%Z
      | Mint16unsigned => 3%Z
      | Mint32 => 4%Z
      | Mint64 => 5%Z
      | Mfloat32 => 6%Z
      | Mfloat64 => 7%Z
      | Many32 => 8%Z
      | Many64 => 9%Z
      end.

Lemma memory_chunk_to_Z_eq x y:
  x = y <-> memory_chunk_to_Z x = memory_chunk_to_Z y.
Proof. Fail sauto. get_gen_statement_for_variables_in_context; sauto. Qed.

End small_examples.


(* 4.2  Combining tactics *)

(* 4.2.1 We first showcase how `snipe` can solve all the examples of
   Section 2 *)

Module solution_examples.

(* Remember that no tactic was able to prove length_rev_app_cons, since
   it involved a combination of arithmetic reasoning on `nat` and
   congruence. `snipe` can solve it, with an additional hypothesis
   `CompDec`: SMTCoq requires all types it reasons about to have a
   decidable equality *)
Lemma length_rev_app_cons :
  forall (B: Type) (HB : CompDec B) (l l' : list B) (b : B),
    length (rev (l ++ (b::l'))) =
      (length l) + (length l') + 1.
Proof. snipe (app_length, rev_length). Qed.

(* sauto and SMTCoq cannot perform case analysis in general, but `snipe`
   does *)
Lemma app_nil_rev B (HB: CompDec B) (l l' : list B) (a : B) : (rev l) ++ l' = nil -> l = [] \/ l' = [].
Proof. snipe. Qed.

Import small_examples.

Import all_ssreflect all_algebra.
Import ZifyClasses ZifyBool ZifyInst ssrZ zify_algebra AlgebraZifyInstances.


(* Thanks to Trakt, `snipe` is able to reason on different types of
   integers, as long as they have been added to Trakt's database *)
Lemma Orderle_int_Zleb_equiv :
  forall (x y : int), (x <= y)%R = Z.leb (Z_of_int x) (Z_of_int y).
Proof. apply (@TBOpInj _ _ _ _ _ _ _ _ _ _ Op_int_le). Qed.

Trakt Add Relation 2 (@Order.le ring_display (Num.NumDomain.porderType int_numDomainType)) Z.leb Orderle_int_Zleb_equiv.

Lemma Orderlt_int_Zltb_equiv :
  forall (x y : int), (x < y)%R = Z.ltb (Z_of_int x) (Z_of_int y).
Proof. apply (@TBOpInj _ _ _ _ _ _ _ _ _ _ Op_int_lt). Qed.

Trakt Add Relation 2 (@Order.lt ring_display int_porderType) Z.ltb Orderlt_int_Zltb_equiv.

Lemma eqint_eqbZ_equiv (x y : int) : x = y <-> Z.eqb (Z_of_int x) (Z_of_int y) = true.
Proof. now rewrite eqint_eqZ_equiv Z.eqb_eq. Qed.

Trakt Add Relation 2 (@eq int) Z.eqb eqint_eqbZ_equiv.

Lemma int_1 : Z_of_int 1 = Zpos 1.
Proof. reflexivity. Qed.

Trakt Add Symbol (GRing.one (Num.NumDomain.porder_ringType int_numDomainType)) (Zpos 1) int_1.
Trakt Add Conversion GRing.one.

Lemma eint : forall (z : int), (z >= 0 -> z < 1 -> z = 0)%R.
Proof. snipe_with_trakt. Qed.

(* It also works in the presence of uninterpreted functions *)
Lemma eq_op_Zeqb (x y:int) : x == y = Z.eqb (Z_of_int x) (Z_of_int y).
Admitted.

Trakt Add Relation 2 (@eq_op int_eqType) Z.eqb eq_op_Zeqb.

Lemma eintcb : forall (f : int -> int) (z : int), (f (z + 1) == f (1 + z))%R.
Proof. snipe_with_trakt. Qed.

End solution_examples.


(* For the use cases of Section 4: see intervals_list.v and confluence.v
   in the same directory *)
