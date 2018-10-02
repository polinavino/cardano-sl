Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Decidable.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Logic.
Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import ProofIrrelevanceFacts.
Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.Structures.OrderedType.
Require Import Bool DecidableType DecidableTypeEx OrderedType Morphisms.
Require Export FMapInterface.
Require Import Coq.Arith.Plus.
Set Implicit Arguments.
Require Import Coq.FSets.FMapFacts.
Hint Extern 1 (Equivalence _) => constructor; congruence.

Generalizable All Variables.


Open Scope list_scope.

(* Proposititonal extensionality, ie. equivalent propositions are equal (found in the ClassicalFacts std lib) *)
Axiom prf_prop_ex : prop_extensionality .
(* proof irrelevance axiom as in ClassicalFacts *)
Axiom proof_irrelevance : forall (A : Prop) (a1 a2 : A), a1 = a2.

(* equality of terms of type A is decidable *)
Definition decA (A:Type) := forall (x y : A), {x = y} + {x <> y}.



(* PRIMITIVE TYPES *)


(* index*)
Definition Ix := nat.

Variable ix1 : Ix.
Variable ix2 : Ix.
Variable ix3 : Ix.
Variable ix4 : Ix.
Variable ix5 : Ix.

(* address *)
Variable Addr : Type.

Variable a1 : Addr.
Variable a2 : Addr.
Variable a3 : Addr.
Variable a4 : Addr.
Variable a5 : Addr.


(* currency value *)
Definition Coin := nat.


(* DERIVED TYPES *)


(* transaction output *)
Definition TxOut : Type := Addr * Coin.

(* collection of finite subsets of A represented by lists *)
Definition Pow (A:Type) := list A.

(* list of outputs *)
Definition Outs : Type := Pow TxOut.

(* finite map as a supsed of A*B *)  
Definition FinMap (A B : Type) := Pow (A*B).


(* proposition that states that a is not in the domain of finite map f *)
Definition not_in_dom `{A : Type} `{B: Type} (a:A) (f : FinMap A B) : Prop :=
  (forall c, ~(In (a,c) f)).


(* a finite map A to B is well-defined whenever for each input there is a single output *)
Inductive wd (A B: Type) : (FinMap A B) -> Prop := 
  | wd0 : wd  nil
  | wd_new : forall a b f, wd  f -> not_in_dom a f 
    -> wd  ((a,b):: f).

(* no duplicate inputs in a finite map *)
Definition ins_unique_f (i : Type) (o : Type) (u : FinMap i o) : Prop := NoDup (fst (split u)).

(* well-defined finite map class *)
Class FinMapWD `{I : Type} `{O : Type} : Type :=
{
  fm : FinMap I O ;
  ins_unique : @ins_unique_f I O fm
}.

Coercion fm : FinMapWD >-> FinMap.

(* transaction output with index Ix *)
Definition IxTxOut : Type := @FinMapWD Ix TxOut.


(* transaction *)
Inductive Tx := MkTx : Pow (Tx * Ix) -> IxTxOut -> Tx.


(* transaction input *)
Definition TxIn : Type := Tx * Ix.

(* powerset of TxIns *)
Definition Ins : Type := Pow TxIn.



(* unspent transaction outputs represented as a finite map *)
Definition UTxO : Type := @FinMapWD TxIn TxOut.



(* Tx's for sanity check examples *)
Variable tx1 : Tx.
Variable tx2 : Tx.
Variable tx3 : Tx.
Variable tx4 : Tx.
Variable tx5 : Tx.

(* tx's 1 to 3 are distinct *)
Variable tx_distinct : 
~(tx1 = tx2) /\ ~(tx1 = tx3) /\ ~(tx2 = tx3).

Notation "# u" := (@fm _ _ u) (at level 50).
Notation "#iu u" := (@ins_unique_f _ _ u) (at level 50).

(* FinMapWD's are equal whenever underlying finite maps are equal *)
Lemma pf_ir_utxo : forall A B (u v : @FinMapWD A B), (#u = #v) -> u = v.
Proof. 
  intros A B u v H. destruct u; destruct v.
  simpl in H. generalize ins_unique0. generalize ins_unique1.
  clear ins_unique0; clear ins_unique1. rewrite H. 
  intros i1 i0. rewrite (proof_irrelevance i0 i1). auto.
Qed.

(* equality of all the types defined above is decidable *)
Parameter decIx : decA Ix.
Parameter decAddr : decA Addr.
Parameter decCoin : decA Coin.
Parameter decTxOut : decA TxOut.
Parameter decTxIn : decA TxIn.
Parameter decTx : decA Tx.
Parameter decUTxO : decA UTxO.

(* A*B is decidable when A and B are *)
Lemma decAB : forall (A B: Type), decA A -> decA B -> decA (A*B).
Proof.
  compute. intros A B dA dB x y. destruct x as (ti1, to1).
  destruct y as (ti2,to2).
  destruct (dA ti1 ti2) as [e1 | e2];
  destruct (dB to1 to2) as [f1 | f2];
  try (rewrite e1; rewrite f1; auto);
  try (rewrite e1); try (right; intro H; inversion H; tauto).
Qed.
  

(* example utxo1 *)
Example utxo1_map := ((tx1, ix1), (a1, 10)) :: ((tx2, ix2), (a2, 20)) :: ((tx3, ix3), (a3, 30)) :: nil.

(* assume utxo1 TxIns distinct *)
Variable pf1 : ins_unique_f utxo1_map.


(* example utxo1 class *)
Example utxo1: UTxO. 
 exists utxo1_map. exact pf1.
Defined.

(* empty UTxO class *)
Example emptyUTxO: UTxO. 
 exists nil. unfold ins_unique_f. constructor. 
Defined.

(*
(* finite map representing utxo1 is well-defined *)
Example utxo1_well_def : wd TxIn TxOut utxo1.
Proof.
  compute. destruct tx_distinct as [H0 [H1 H2]]. 
  apply wd_new; try ( apply wd_new); try ( apply wd_new); 
  try ( apply wd0); try compute; try intros; try tauto;
  try (inversion H as [H01 | H02]); try (inversion H01 as [(p1,p2)]);
  try (symmetry in p1); try tauto.
  inversion H02 as [H3 | H4]; try ( inversion H3 as [(p1,p2)]);
  try (symmetry in p1); try tauto.
Qed.
*)


(* block *)
Definition Block := Pow Tx.

(* pending transactions *)
Definition Pending := Pow Tx.


(* FILTERED SETS *)

(* our addresses *)
Variable ours : Addr -> bool.

(* our unspent transaction outputs *)
Definition TxOuts_ours (outs : Outs) := filter (fun a => ours (fst a)) outs.

(*
Fixpoint TxOuts_ours (outs : Outs) := 
  match outs with
  | nil => nil
  | a :: l => if ours (fst a) then a :: TxOuts_ours l else TxOuts_ours l
  end.*)

(* OPERATIONS ON UTxO *)

(* disjoint union of UTxOs *)
Definition unionUTxO (u v : UTxO) (pf :#iu (#u++#v)) : UTxO. 
  exists ((# u)++(# v)). auto.
Defined.

(* compute elements in both lists *)
Fixpoint in_both (A : Type) (dA : decA A) (l1 : list A) (l2: list A) : list A :=
  match l1 with
    | nil => nil
    | x::xs => if in_dec dA x l2 then  x::(in_both dA xs l2) else (in_both dA xs l2)
  end.

(* element in_both if it is In both *)
Definition in_both_lem (A : Type) (dA : decA A) (l1 : list A) (l2: list A) (a:A) : 
In a (in_both dA l1 l2) <-> (In a l1 /\ In a l2).
Admitted.

(* intersection of Ins *)
Definition interIns (u v : Ins) : Ins := 
  in_both decTxIn u v.

(* union of Ins *)
Definition unionIns (u v : Ins) : Ins := 
  (u ++ v).

(* compute elements in only one of the lists *)
Fixpoint exclIns (r l : Ins) : Ins :=
  match l with
    | nil => r
    | x::xs => exclIns (@remove TxIn decTxIn x r)  xs
  end.

(* domain of a utxo *)
Definition dom (u : UTxO) := fst (split (# u)).

(*
(* any subset of a UTxO is still a finite map *)
Definition UTxO_r (p p' : Prop) (utxo : UTxO) :
  (forall a b c, (((utxo (a, b))) /\ ((utxo (a, c))) -> b=c))  ->
  (forall a b c, (((utxo (a, b)) /\ p) /\ ((utxo (a, c)) /\ p')-> b=c)).
Proof.
  intros. apply (H a b c). tauto.
Qed.
*)

(* domain restriction *)
Fixpoint d_r_fm (ins : Ins) (u : FinMap TxIn TxOut) : FinMap TxIn TxOut :=
  match u with
  | nil => nil
  | io::v => (if (in_dec decTxIn (fst io) ins) then (io :: d_r_fm ins v) else (d_r_fm ins v))
  end.


Lemma split_one : forall (A B:Type), forall (a:A*B), forall (l:list (A*B)),
  (fst (split (a::l))) = ((fst a)::(fst (split l))).
Proof.
  intros A B a l. 
  replace (split (a::l)) with ((fst a)::(fst (split l)), (snd a)::(snd (split l))).
  simpl. auto. destruct a as (a,b).
 compute. destruct ((fix split (l0 : list (A * B)) : list A * list B :=
       match l0 with
       | nil => (nil, nil)
       | (x, y) :: tl => let (left, right) := split tl in (x :: left, y :: right)
       end)). auto.
Qed.

(* in u implies in d_r u *)
Lemma in_dr : forall a u ins, In a (fst (split (d_r_fm ins u))) ->
  In a (fst (split u)).
Proof.
  intros a u ins H. induction u. compute in H. auto.
  rewrite split_one.
  simpl.  simpl in H. destruct (in_dec decTxIn (fst a0) ins).
  rewrite split_one in H; simpl in H. tauto. tauto. 
Qed.

(* in u implies in d_r u *)
Lemma in_dr_n : forall a u ins, ~ In a (fst (split u)) ->
  In a (fst (split (d_r_fm ins u))) -> False.
Proof.
  intros a u ins H1 H2. generalize (in_dr a u ins). tauto.
Qed.
  

(* domain restriction of FM is still well-def *)
Definition d_r_ins_dist (ins : Ins) (u : @FinMapWD TxIn TxOut) : ins_unique_f (d_r_fm ins (#u)).
Proof.
  unfold ins_unique_f. destruct u as (u,pf). induction u. compute. constructor.
  simpl. destruct (in_dec decTxIn (fst a) ins); 
  unfold ins_unique_f in pf; rewrite split_one in pf;
  simpl in IHu; inversion pf; try ( rewrite split_one);
  try (constructor; intro nd; apply (in_dr_n (fst a) u ins)); auto;
  try constructor; try (apply IHu; unfold ins_unique_f; auto).
  intro nd. apply (in_dr_n (fst a) u ins); auto.
Qed.

Definition d_r (ins : Ins) (u : UTxO) : UTxO.
exists (d_r_fm ins (# u)). exact (d_r_ins_dist ins u).
Defined.


(* domain exclusion *)
Fixpoint d_e_fm (ins : Ins) (u : FinMap TxIn TxOut) : FinMap TxIn TxOut :=
  match u with
  | nil => nil
  | io::v => (if (in_dec decTxIn (fst io) ins) then (d_e_fm ins v) else (io :: d_e_fm ins v) ) 
  end.  

(* in ins implies not in d_e_fm *)
Lemma in_ins_de : forall a u ins, In a (fst (split (d_e_fm ins u))) -> 
  In a (fst (split u)).
Proof.
  intros a u ins H. induction u. compute in H. auto.
  rewrite split_one.
  simpl.  simpl in H. destruct (in_dec decTxIn (fst a0) ins); try tauto.
  rewrite split_one in H; simpl in H. tauto.  
Qed.

(* domain exclusion of UTxO is w.d. *)
Definition d_e_ins_dist (ins : Ins) (u : UTxO) : ins_unique_f (d_e_fm ins (# u)).
  unfold ins_unique_f. destruct u as (u,pf). induction u. compute. constructor.
  simpl. destruct (in_dec decTxIn (fst a) ins); 
  unfold ins_unique_f in pf; rewrite split_one in pf;
  simpl in IHu; inversion pf; try ( rewrite split_one);
  try (constructor); try (intro nd);
  unfold ins_unique_f in IHu; try (apply IHu); unfold ins_unique_f; auto.
  generalize (in_ins_de (fst a) u ins). tauto.
Qed.

Definition d_e (ins : Ins) (u : UTxO) : UTxO.
exists (d_e_fm ins (# u)). exact (d_e_ins_dist ins u).
Defined.

(* range restriction *)
Fixpoint r_r_fm (u : FinMap TxIn TxOut) (outs : Outs)  : FinMap TxIn TxOut :=
  match u with
  | nil => nil
  | io::v => (if (in_dec decTxOut (snd io) outs) then (io :: r_r_fm v outs) else (r_r_fm v outs)) 
  end.

(* special case of range restriction to only our addresses *)
Fixpoint r_r_ours_fm (u : FinMap TxIn TxOut) : FinMap TxIn TxOut :=
  match u with
  | nil => nil
  | a::v => if ours (fst (snd a)) then a :: r_r_ours_fm v else r_r_ours_fm v
  end.
(*
  filter (fun io => (ours (fst (snd io)))) u.
*)

Definition in_ins_rr : forall a u outs, ~ In a (fst (split u)) ->
  (~ In a (fst (split (r_r_fm u outs)))) /\ (~ In a (fst (split (r_r_ours_fm u)))).
Proof.
  intros a u outs H. split; induction u; try (compute in H; tauto);
  rewrite split_one in H; unfold r_r_fm; unfold r_r_ours_fm; simpl;
  simpl in H; intro H2; apply IHu; try (intro H3); try tauto.
  destruct (in_dec decTxOut (snd a0) outs);
  try (rewrite split_one in H2); try (inversion H2); try tauto;
  unfold r_r_fm; try tauto.
  destruct (ours (fst (snd a0)));
  try (rewrite split_one in H2); try (inversion H2); try tauto;
  unfold r_r_ours_fm; try tauto.
Qed.

Ltac rr_dist a u outs IHu := 
  rewrite split_one; constructor; try (intro nd); 
  try (apply IHu); unfold ins_unique_f; try tauto;
  try (generalize (in_ins_rr (fst a) u outs)); try tauto.

Definition r_r_ins_dist (u : UTxO) (outs : Outs) : 
    ins_unique_f (r_r_fm u outs) /\ ins_unique_f (r_r_ours_fm u).
  split; unfold ins_unique_f; destruct u as (u,pf); induction u; 
  try (unfold ins_unique_f in IHu);
  try ( compute; constructor); simpl;
  unfold ins_unique_f in pf; rewrite split_one in pf;
  simpl in IHu; inversion pf.
  destruct (in_dec decTxOut (snd a) outs).
  rr_dist a u outs IHu. tauto.
  destruct (ours (fst (snd a))). 
  rr_dist a u outs IHu. tauto.
Qed.

Definition r_r (u : UTxO) (outs : Outs): UTxO.
exists (r_r_fm (# u) outs). apply (r_r_ins_dist u outs).
Defined.


Definition r_r_ours (u : UTxO) : UTxO.
exists (r_r_ours_fm (# u)). apply (r_r_ins_dist u). exact nil.
Defined.


(* sanity checks assuming all primitive types are nat's *)
(* domain of utxo1 *)
Example dom_utxo1 : Pow TxIn := 
    (tx1, ix1)::(tx2, ix2)::(tx3, ix3)::(@nil TxIn).

(* domain defined in dom_utxo1 is the same as computed by dom function *)
Fact dom_utxo1_pf :
  dom utxo1 = dom_utxo1.
Proof.
  reflexivity.
Qed.


(*
(* ins (id1, ix1) which maps to |-> (a1, 10) and (id3, ix3) which maps to |-> (a3, 30) *)
Example d_r_utxo1_ins12 : UTxO :=
  ((tx1, ix1), (a1, 10)) :: ((tx3, ix3), (a3, 30)) :: nil.



(* domain restriction of utxo1 to ins 0 and 3 *)
Example drutxo1_ins : Pow TxIn :=
 (tx1, ix1) :: (tx3, ix3) :: nil.


(* domain restriction defined by drutxo1_ins for ins defined by d_r_utxo1_ins12 
   the same as computed by d_r function *)
Example d_r_utxo1_ins12_pf :
   d_r_utxo1_ins12 = (d_r drutxo1_ins utxo1).
Proof.
  unfold utxo1. unfold d_r_utxo1_ins12.
  unfold drutxo1_ins. unfold d_r. compute.
  compute. apply functional_extensionality. intro. apply prf_prop_ex. destruct x; simpl.
  split; try split; try tauto.
  inversion H; try (inversion H0); try tauto. intro.
  inversion H as [[H1 | [H2 | H2']] [H3 | H4]]; try tauto; 
  destruct txid_distinct; inversion H2; destruct p; 
  inversion H5 as [(H7,H8)]; try (inversion H3 as [(H9, H10)]);
  try (inversion H4 as [(H9, H10)]);
  rewrite H9 in H7; try tauto; symmetry in H7; try tauto.
Qed.
*)

Definition UTxOinc_fm (u v : FinMap TxIn TxOut) : Prop :=
  forall (io:(TxIn*TxOut)), In io u -> In io v.

(* subset of outputs in a UTxO, ie. forall io : (tx,i) |-> (addr, c) \in u , io \in v *)
Definition UTxOinc (u v : UTxO) : Prop :=
  forall (io:(TxIn*TxOut)), In io (# u) -> In io (# v).

Definition UTxOeq_fm u v : Prop := 
  (UTxOinc_fm u v) /\ (UTxOinc_fm v u).

(* instead of '=', we use : two UTxOs are equal when each contains the other *)
Definition UTxOeq (u v : UTxO) : Prop := (UTxOinc u v) /\ (UTxOinc v u).

(* subset of the transactions in the UTxO *)
Definition S_UTxOinc (u v : UTxO) : Prop :=
  (UTxOinc u v) /\
  (forall (io io':(TxIn*TxOut)), In io (# u) -> In io' (# v) 
    -> (fst (fst io) = fst (fst io')) -> In io' (# u)).

(* rewrite using UTxOeq lemma *)
Lemma utxo_eq_fst_sp : forall t u v, UTxOeq u v -> 
  ((In t (fst (split (# u)))) <-> (In t (fst (split (# u))))).
Proof.
  intros t u v. destruct u; destruct v. unfold UTxOeq. unfold UTxOinc.
  simpl. intro H. destruct H as [H1 H2]. induction t.

Admitted.


  

(* PROPERTIES OF UTxO OPERATIONS *)


(* split snd rewrite *)
Lemma split_snd : forall (A B:Type), forall (a:A*B), forall (l:list (A*B)),
  (snd (split (a::l))) = ((snd a)::(snd (split l))).
Proof.
  intros A B a l. 
  replace (split (a::l)) with ((fst a)::(fst (split l)), (snd a)::(snd (split l))).
  simpl. auto. destruct a as (a,b).
 compute. destruct ((fix split (l0 : list (A * B)) : list A * list B :=
       match l0 with
       | nil => (nil, nil)
       | (x, y) :: tl => let (left, right) := split tl in (x :: left, y :: right)
       end)). auto.
Qed.


(* tactics for proving properties 1 to 9 *)
Ltac prove_prop io a H utxo0 IHutxo0 ins_unique0 := 
  simpl; simpl in H; auto; simpl in IHutxo0;
  try (destruct (in_dec decTxIn (fst a) io));
  try (destruct (in_dec decTxOut (snd a) io)); 
  simpl in H;
  unfold ins_unique_f in ins_unique0;
  rewrite split_one in ins_unique0; inversion ins_unique0 as [H11 | H12]; 
  try (inversion H); try tauto;
  apply or_intror. 

Ltac prove_eq_props1 u v :=
  unfold interIns; unfold unionUTxO;
  unfold UTxOeq; unfold UTxOinc; unfold dom;
  split; try (intros io H); unfold d_r; unfold d_r_fm; 
  destruct u as (utxo0, ins_unique0); try (destruct v as (utxo1, ins_unique1)); simpl.
 

Ltac prove_eq_props2 a ins pf ins_unique0 H IHutxo0 := 
  unfold In in H; unfold d_r_fm in H; simpl in H;
  unfold In; unfold ins_unique_f in ins_unique0; simpl; auto;
  unfold In in IHutxo0; unfold ins_unique_f in IHutxo0; 
  simpl in IHutxo0; simpl in pf;
  try (rewrite split_one in ins_unique0); try (inversion ins_unique0);
  destruct (in_dec decTxIn (fst a) ins);
  unfold ins_unique_f in pf; try (rewrite split_one in pf); try (inversion pf); simpl;
  simpl in H; try tauto. 

(* property 1 *)
Definition UTxO_prop1 : forall (ins : Pow TxIn) (u : UTxO),
  UTxOinc (d_r ins u) u.
Proof.
  intros ins u. intros io H.
  destruct u as (utxo0, ins_unique0); induction utxo0; prove_prop ins a H utxo0 IHutxo0 ins_unique0.
Qed.

(* property 2 *)
Definition UTxO_prop2 : forall (ins : Pow TxIn) (u : UTxO),
  UTxOinc (d_e ins u) u.
Proof.
  intros ins u. intros io H.
  destruct u as (utxo0, ins_unique0); induction utxo0; prove_prop ins a H utxo0 IHutxo0 ins_unique0.
Qed.

(* property 2 *)
Definition UTxO_prop2_fm : forall (ins : Pow TxIn) u,
  incl (d_e_fm ins u) u.
Proof.
  Admitted.

(* property 2 with dom *)
Definition UTxO_prop_dom2 : forall (ins : Pow TxIn) (u : UTxO),
  incl (dom (d_e ins u)) (dom u).
Proof.
  intros ins u. generalize (UTxO_prop2 ins u).
  unfold UTxOinc. unfold d_e. unfold dom. destruct u. simpl.
  intros p2 io H. 
  generalize in_split_l .
(*  destruct u; induction utxo0 ; prove_prop ins a H utxo0 IHutxo0 ins_unique0.*)
Admitted.

(* property 3 *)
Definition UTxO_prop3 : forall (u : UTxO) (outs : Pow TxOut),
  UTxOinc (r_r u outs) u.
Proof.
  intros u outs. intros io H.
  destruct u as (utxo0, ins_unique0); induction utxo0; prove_prop outs a H utxo0 IHutxo0 ins_unique0.
Qed.

(* auxiliary lemma about ins_unique *)
Lemma vzin : forall A B (v z : FinMap A B) a, ins_unique_f (v ++ z) -> (In a v) -> ~ In (fst a) (fst (split z)).
Proof.
  intros A B v z a Hvz Hv. intro Hz. 
  induction v. inversion Hv.
  apply IHv. unfold ins_unique_f in Hvz. 
  unfold app in Hvz. rewrite split_one in Hvz. inversion Hvz.
  unfold ins_unique_f. unfold app. exact H2.
  inversion Hv. 
  rewrite H in Hvz. unfold ins_unique_f in Hvz.
Admitted.

(* some auxiliary lemmas for upcoming properties *)

(* similar to utxo_eq_fst_sp, need to make them into one / rename *)
Lemma ina_split : forall A B (a:(A*B)) (u:list (A*B)), In a u -> In (fst a) (fst (split u)).
Proof.
  intros A B a u Hiau. destruct a as (a,b). 
  induction u. simpl. inversion Hiau. 
  rewrite split_one. simpl in IHu. simpl.
  inversion Hiau; destruct a0 as (a0,b0); simpl.  
  inversion H. tauto. tauto.
Qed. 


Lemma in_split : forall A B (a:A) (w z:list (A*B)), (forall ab, In ab w -> In ab z) -> In a (fst (split w)) 
  -> In a (fst (split z)).
Proof.
  intros A B a w z Hinwz Hisw. 
 Admitted.

Lemma in_dist : forall A (a:A) l m, In a (l++m) <-> (In a l) \/ (In a m).
Proof.
  intros A a l m. split; intro Hp; 
  induction l; try (rewrite app_nil_l in Hp); 
  simpl; simpl in Hp; try tauto.
Qed.


Lemma inv_orw : forall A B (a:(A*B)) (u w:list (A*B)), In (fst a) (fst (split (u ++ w))) -> 
    (In (fst a) (fst (split u)) \/ In (fst a) (fst (split w))).
Admitted.


Lemma sub_utxo_nodup : forall u v w z, UTxOinc u v -> UTxOinc w z ->
  #iu ((# v)++(# z)) ->#iu ((# u)++(# w)).
Proof.
  intros u v w z.
  destruct v as [v vpf]; destruct u as [u upf]; destruct w as [w wpf]; destruct z as [z zpf].
  unfold UTxOinc. simpl. intros Hiu Hiz Hpl. induction u; simpl; auto.
  unfold ins_unique_f. rewrite split_one. constructor 2.
  unfold ins_unique_f in upf. rewrite split_one in upf. inversion upf.
  assert (Hav : In a v). apply Hiu. simpl. tauto.

  assert (Hniz : ~ In (fst a) (fst (split z))).
  apply (vzin v z); auto.
  assert (~ In (fst a) (fst (split w))).
  intro. generalize (in_split (fst a) w z (Hiz) H3). tauto.
  intro. generalize (inv_orw a u w). tauto.

  unfold ins_unique_f in IHu. apply IHu.
  unfold ins_unique_f in upf. rewrite split_one in upf. inversion upf. auto.
  intros io Hu. apply Hiu. unfold In. unfold In in Hu. tauto.
Qed.
 

(* property 4 *)
Definition UTxO_prop4 : forall (ins : Ins) (u v : UTxO) (pf :#iu ((# u)++(# v))),  
  UTxOeq (d_r ins (unionUTxO u v pf)) (unionUTxO (d_r ins u) (d_r ins v) 
    (@sub_utxo_nodup (d_r ins u) u (d_r ins v) v (UTxO_prop1 ins u) (UTxO_prop1 ins v) pf)).
Proof.
  intros ins u v pf; prove_eq_props1 u v; induction utxo0; 
  prove_eq_props2 a ins pf ins_unique0 H IHutxo0.
Qed.

(*
(* property 4 *)
Definition UTxO_prop4 : forall (ins : Ins) (u v : UTxO) (pf :#iu ((# u)++(# v))),  
  (d_r ins (unionUTxO u v pf)) = unionUTxO (d_r ins u) (d_r ins v) 
    (@sub_utxo_nodup (d_r ins u) u (d_r ins v) v (UTxO_prop1 ins u) (UTxO_prop1 ins v) pf).
  (*  (d_r_u_disj ins u v pf).*)
Proof.
  intros ins u v pf. unfold unionUTxO. 
  rewrite (pf_ir_utxo (d_r ins {| utxo := (# u) ++ (# v); ins_unique := pf |})
({| utxo := (# (d_r ins u)) ++ (# (d_r ins v)); ins_unique := (sub_utxo_nodup (UTxO_prop1 ins u) (UTxO_prop1 ins v) pf) |})).
(*d_r_u_disj ins u v pf *)
  auto. simpl.
  destruct u; destruct v; simpl. induction utxo0. simpl.
  auto.
  simpl. unfold d_r_fm.
  unfold d_r_fm in IHutxo0. simpl in IHutxo0.
  rewrite IHutxo0; auto; unfold ins_unique_f in ins_unique0; simpl in pf;
  rewrite split_one in ins_unique0; inversion ins_unique0; 
  unfold ins_unique_f; unfold ins_unique_f in pf;
  rewrite split_one in pf; inversion pf;
  destruct (in_dec decTxIn (fst a) ins); simpl; auto.
Qed.*)

(* property 5 *)
Definition UTxO_prop5 : forall (ins : Ins) (u v : UTxO) (pf :#iu ((# u)++(# v))), 
  UTxOeq (d_e ins (unionUTxO u v pf)) (unionUTxO (d_e ins u) (d_e ins v)
(@sub_utxo_nodup (d_e ins u) u (d_e ins v) v (UTxO_prop2 ins u) (UTxO_prop2 ins v) pf)).
Proof.
  intros ins u v pf; prove_eq_props1 u v; induction utxo0; 
  prove_eq_props2 a ins pf ins_unique0 H IHutxo0.
Qed.

(*
Definition UTxO_prop5_fm : forall ins u v
  UTxOeq (d_e ins (unionUTxO u v pf)) (unionUTxO (d_e ins u) (d_e ins v)
(@sub_utxo_nodup (d_e ins u) u (d_e ins v) v (UTxO_prop2 ins u) (UTxO_prop2 ins v) pf)).
*)

(*
Lemma in_both_in : forall (a:(TxIn*TxOut)) (ins:Ins) u, In (fst a) ins -> ((d_r_fm (fst a :: in_both decTxIn (fst (split u)) ins) u) 
    = (d_r_fm (in_both decTxIn (fst (split u)) ins) u)).
Proof.
  intros a ins u Hin. unfold d_r_fm. induction u. simpl. auto.
  simpl.
  destruct (in_dec decTxIn (fst a0) (in_both decTxIn (fst (let (x, y) := a0 in let (left, right) := split u in (x :: left, y :: right))) ins)).
  destruct (match decTxIn (fst a) (fst a0) with
    | left e => left (or_introl e)
    | right _ => left (or_intror i)
    end).  simpl. *)

Lemma a_in_both : forall a utxo ins,
  (d_r_fm (in_both decTxIn (fst a :: fst (split utxo)) ins) (a::utxo)) = 
   (a :: (d_r_fm ((in_both decTxIn (fst (split utxo)) ins)) utxo)).
Proof.
Admitted.

(* these can mostly be proved with the Ltacs defined above - I will fill this in this week *)

(* property 6 *)
Definition UTxO_prop6 : forall (ins : Ins) (u : UTxO), 
  UTxOeq (d_r (interIns (dom u) ins) u) (d_r ins u).
Proof.
  intros ins u. 
Admitted.


(* property 7 *)
Definition UTxO_prop7 : forall (ins : Ins) (u v : UTxO), 
  UTxOeq (d_e (interIns (dom u) ins) u) (d_e ins u).
Proof.
Admitted.

(* property 8 *)
Definition UTxO_prop8 : forall (ins : Ins) (u v : UTxO) (pf :#iu ((# u)++(# v))), 
  UTxOeq (d_e (unionIns (dom u) ins) (unionUTxO u v pf))  (d_e (unionIns (dom u) ins) v).
Proof.
Admitted.

(* property 9 *)
Definition UTxO_prop9 : forall (ins : Ins) (u : UTxO), 
  UTxOeq (d_e ins u) (d_r (exclIns (dom u) ins) u).
Proof.
Admitted. 

Lemma d_r_e_unique : forall u ins,#iu ((# (d_e ins u))++(# (d_r ins u))).
Proof.
Admitted.

(* property 10 added *)
Definition UTxO_prop10 : forall (ins : Ins) (u : UTxO) , 
  UTxOeq (unionUTxO (d_e ins u) (d_r ins u) (d_r_e_unique u ins)) u.
Proof. 
Admitted.

(* property 11 added *)
Definition UTxO_prop11 : forall (ins : Ins) (u : UTxO), 
  UTxOeq (d_r (interIns (dom (d_e ins u)) (dom (d_r ins u))) u) emptyUTxO.
Proof.
Admitted.

(* property 12 added *)
Definition UTxO_prop12 : forall (u v : UTxO) pf, 
  unionIns (dom v) (dom u) = dom (unionUTxO u v pf).
Proof.
Admitted.

(* AUXILIARY OPERATIONS *)

(* txins map defined *)
Fixpoint txins (txs : Pow Tx) : Ins := 
  match txs with
  | nil => nil
  | tx::xs => 
    match tx with
    | MkTx l o =>  l ++ (txins xs)
    end
  end.

(* build the finite map part of a UTxO from the outputs of one Tx *)
Fixpoint makeUTxOforTx (tx : Tx) (outs : FinMap Ix TxOut) : FinMap TxIn TxOut :=
  match outs with 
  | nil => emptyUTxO
  | o :: l => ((tx, fst o), (snd o)) :: makeUTxOforTx tx l
  end.

Lemma in_a_mkUTxO : forall a o_f tx, ~ In a (fst (split o_f)) -> 
  In (tx, a) (fst (split (makeUTxOforTx tx o_f)))  -> False.
Proof.
  intros a o_f tx H1 H2. induction o_f. compute in H1. auto.
  rewrite split_one in H1. simpl in H1.
  unfold makeUTxOforTx in H2. rewrite split_one in H2.
  apply IHo_f; try tauto; try (inversion H2); try tauto.
  simpl in H. inversion H. tauto.
Qed. 


(* prove makeUTxOforTx f.m. is well-defined *)
Definition wd_makeUTxOforTx : forall tx (outs : IxTxOut), @ins_unique_f _ _ (makeUTxOforTx tx (# outs)).
Proof.
  intros tx outs. destruct outs as (o_f, i_u). simpl.
  unfold makeUTxOforTx. unfold ins_unique_f. induction o_f.
  compute. constructor. 
  unfold ins_unique_f in i_u.
  rewrite split_one in i_u.  
  rewrite split_one. simpl. constructor;
  try (inversion i_u); try tauto. intro.
  apply (in_a_mkUTxO (fst a) o_f tx);
  unfold makeUTxOforTx; try tauto.
Qed.

(* compute the f.m. for txouts *)
Fixpoint txouts_calc (txs : Pow Tx) : FinMap TxIn TxOut :=
  match txs with
  | nil => nil
  | tx::xs => 
      (match tx with
      | MkTx ins outsix => makeUTxOforTx tx outsix end)
    ++(txouts_calc xs)
  end.

(* aux lemmas *)
Lemma split_app : forall A B (u v : list (A*B)), fst (split (u ++ v)) = fst (split u) ++ fst (split v).
Proof.
  intros A B u v. induction u. compute. auto.
  rewrite split_one. 
Admitted.

Lemma split_app2 : forall A B (u v : list (A*B)), snd (split (u ++ v)) = snd (split u) ++ snd (split v).
Proof.
  intros A B u v. induction u. compute. auto.
Admitted.

(* w.d. property NOT implied from w.d. each makeUTxOforTx *)
(* additional constraints required *)
(* do they need to be more fine-grain than txouts_unique parameter below?? *)
(* for ex. inductively defined Prop in terms of makeUTxOforTx *)
Definition txouts (txs : Pow Tx) (txouts_unique : ins_unique_f (txouts_calc txs)) : UTxO.
exists (txouts_calc txs).
apply txouts_unique.
Defined.


Open Scope nat_scope.

(* balance *)
Fixpoint balance_calc (u : Pow (TxIn*TxOut)) : nat :=
  match u with
  | nil => 0
  | io::l => (snd (snd io)) + (balance_calc l)
  end.

Definition balance (u : UTxO) := balance_calc (# u).

(* depends on Prop *)
Definition depends_on (t1 t2 : Tx) : Prop :=
  exists ix, In (t1,ix) (txins (t2::nil)). 

(* is this provable from txouts_unique directly? no *)
(* what conditions can /need to be imposed on the tx list for  this to be provable? *)
(* must be equal  snd(split i) and fst(split #o) ?*)
Definition independent (txs : Pow Tx) (txouts_unique : ins_unique_f (txouts_calc txs)) : Prop :=
  interIns (txins txs) (dom (txouts txs txouts_unique)) = nil.

(* lemma numbers match original wallet spec document (not my pdf) *)
Lemma lemma161 :  forall u v pf, balance (unionUTxO u v pf) = (balance u) + (balance v).
Proof.
  intros u v pf. destruct u as (u, upf); destruct v as (v, vpf).
  unfold unionUTxO. unfold balance. simpl.
  unfold balance_calc. induction u. compute. auto.
  simpl. simpl in IHu. rewrite IHu. 
  rewrite plus_assoc. reflexivity.
  unfold ins_unique_f in upf. generalize upf. clear.
  intro upf. rewrite split_one in upf. inversion upf.
  auto. simpl in pf. 
  unfold ins_unique_f in pf. rewrite split_one in pf. inversion pf.
  auto.
Qed.

Lemma lemma162 :  forall u ins, balance (d_e ins u) = (balance u) - (balance (d_r ins u)).
Proof.
Admitted.


(* WALLET STATE *)

Definition Wallet : Type := UTxO * Pending.

Definition empty_w : Wallet := (emptyUTxO, @nil Tx).

(* AUXILIARY FUNCTIONS *)

Definition available (w : Wallet) := d_e (txins (snd w)) (fst w).


Definition change (pending : Pending) (txouts_unique : ins_unique_f (txouts_calc pending)) := 
  r_r_ours (txouts pending txouts_unique).

(* again, here need to assume utxo and (available w) (change (snd w)) are disjoint? *)
Definition total (w : Wallet) (txouts_unique : ins_unique_f (txouts_calc (snd w))) pf : UTxO := 
  unionUTxO (available w) (change (snd w) txouts_unique) pf.


Definition new (b : Block) (u : UTxO) (txouts_unique : ins_unique_f (txouts_calc b)) : UTxO 
  := d_e (txins b) (r_r_ours (txouts b txouts_unique)).

(* need to assume utxo and (r_r ...) are disjoint? *)
Definition updateUTxO (b: Block) (u: UTxO) (txouts_unique : ins_unique_f (txouts_calc b)) pf := 
  d_e (txins b) (unionUTxO u (r_r_ours (txouts b txouts_unique)) pf).

Definition empty_inter (l1 l2 : Ins) : bool :=
  match interIns l1 l2 with
  | nil => true
  | t :: l => false
  end.

Lemma empty_nodup : forall l1 l2, (empty_inter l1 l2) = true <-> NoDup (l1 ++ l2).
Proof.
  Admitted.

Definition ins_tx (tx : Tx) :=
  match tx with
  | MkTx inputs outputs => inputs
  end.

Fixpoint updatePending (b : Block) (pending : Pending) : Pending :=
  match b with
  | nil => nil
  | tx :: l => if (in_dec decTx tx pending) then (if (empty_inter (ins_tx tx) (txins b))
    then tx :: (updatePending l pending) else (updatePending l pending)) else (updatePending l pending)
  end.


(* ATOMIC UPDATES *)

Definition applyBlock (b : Block) (w : Wallet) (txouts_unique : ins_unique_f (txouts_calc b)) pf
  (precond : (interIns (dom (txouts b txouts_unique)) (dom (fst w))) = nil) : Wallet
  := (updateUTxO b (fst w) txouts_unique pf, updatePending b (snd w)). 

Definition newPending (tx : Tx) (w : Wallet) (precond : forall i, In i (ins_tx tx) -> In i (dom (available w)))
  := ((fst w), tx :: (snd w)).

(*
Inductive atomic_updates_rel (w : Wallet) : Prop :=
  | is_em : w = empty_w
  | app_b : forall b (t_u : ins_unique_f (txouts_calc b)) pf precond, 
      atomic_updates_rel w -> atomic_updates_rel (applyBlock b w t_u pf precond)
  | new_pen : forall tx precond, atomic_updates_rel w -> atomic_updates_rel (newPending tx w precond).
*)

Inductive atomic_updates_rel : Wallet -> Prop :=
  | is_em : atomic_updates_rel empty_w
  | app_b : forall b w (t_u : ins_unique_f (txouts_calc b)) pf precond, 
      atomic_updates_rel w -> atomic_updates_rel (applyBlock b w t_u pf precond)
  | new_pen : forall tx w precond, atomic_updates_rel w -> atomic_updates_rel (newPending tx w precond).


(* QUERIES *)

Definition availableBalance (w : Wallet) := balance (available w).


Definition totalBalance (w : Wallet) pf t_u := balance (total w pf t_u).

(* Lemma 3.3 *)
Lemma lemma33 : forall b pending t, In t (updatePending b pending) -> In t pending.
Proof.
  intros b pending t in_t. unfold updatePending in in_t.
  induction b. inversion in_t.
  destruct (in_dec decTx a pending);
  destruct ( empty_inter (ins_tx a) (txins (a :: b)));
  try (inversion in_t as [H1 | H2]); try (rewrite <- H1; auto); 
  try (apply IHb; auto).
Qed. 


(* aux lemmas *)
Lemma d_e_fm_nil : forall utxo, d_e_fm nil utxo = utxo.
Proof. 
  intro utxo. 
  induction utxo. compute. auto.
  simpl. rewrite IHutxo; auto.
Qed.

Lemma r_r_ours_dist : forall ou ou1, (r_r_ours_fm (ou ++ ou1)) = (r_r_ours_fm ou ++ r_r_ours_fm ou1).
Admitted.

Lemma r_r_ours_union : forall u v, (ins_unique_f ((# u)++(# v))) -> 
  ins_unique_f ((# (r_r_ours u)) ++ (# (r_r_ours v))). 
Admitted.

Lemma r_r_ours_dist_u : forall u v pf, (r_r_ours (unionUTxO u v pf)) = 
  (unionUTxO (r_r_ours u) (r_r_ours v) (r_r_ours_union u v pf)).
Proof. 
  intros u v pf. apply pf_ir_utxo. unfold r_r_ours. unfold unionUTxO.
  destruct u. destruct v. simpl. apply r_r_ours_dist.
Qed.

Definition range : UTxO -> list TxOut
  := fun u : UTxO => snd (split (#u)).

(* aux lemmas *)
Lemma in_snd_app : forall t ins u v,
  In t (snd (split (d_e_fm ins (u++v)))) <-> ((In t (snd (split (d_e_fm ins u)))) \/
    (In t (snd (split (d_e_fm ins v))))).
Proof.
  Admitted. 

Lemma in_snd_sub : forall t (u v : FinMap TxIn TxOut), incl u v ->
  In t (snd (split u)) -> (In t (snd (split v))). 
Proof.
  Admitted. 

Lemma in_snd_sub_de : forall t u ins,
  In t (snd (split (d_e_fm ins u))) -> (In t (snd (split u))). 
Proof.
  intros t u ins H. apply (@in_snd_sub t (d_e_fm ins u) u); auto.
   apply UTxO_prop2_fm.
Qed.

Lemma excl_i : forall i o v ins,
 incl (d_e_fm (i++ins) ((r_r_ours_fm (makeUTxOforTx (MkTx i o) o)) ++ v))
  (d_e_fm (i++ins) v).
Proof.
  intros i o v ins. intros t H.
  induction i. simpl in H. unfold makeUTxOforTx in H.
   compute.
Admitted.

(* working on this - numbering matches wallet-spec paper *)
(* Invariant 3.4 *)
Lemma pending_in_dom : forall w (at_up : atomic_updates_rel w), 
  incl (txins (snd w)) (dom (fst w)).
Proof.
  intros w ar t. intro H.
  induction ar; simpl; auto.

  unfold applyBlock; unfold updateUTxO; unfold updatePending;
  unfold applyBlock in H; unfold updateUTxO in H; unfold updatePending in H.
  simpl in H.
  induction b. unfold txins in H. inversion H.
Admitted.

(* working on this *)
(* Invariant 3.5 *)
Lemma invarian35 : forall w (at_up : atomic_updates_rel w), 
  incl (range (fst w)) (TxOuts_ours (range (fst w))).
Proof.
  intros w a_u. intros t H. unfold range.
  induction a_u. compute in H; auto.
  apply filter_In; split; auto. unfold TxOuts_ours in IHa_u.
  rewrite filter_In in IHa_u. unfold applyBlock in H.
  unfold updateUTxO in H. unfold range in H.
  unfold updatePending in H. simpl in H.
  rewrite in_snd_app in H. inversion H as [H1 | H2].
  apply IHa_u; auto. unfold range. 
  destruct w as (u,p). destruct u as (u,pfu). 
  simpl; simpl in H1. generalize H1. clear.
  intro H1. apply (in_snd_sub_de t u (txins b)). auto.
  generalize H2. clear. intro H2.
  induction b. compute in H2. auto.
  apply IHb. destruct a as (i,o). simpl in H2. 
  rewrite r_r_ours_dist in H2.
Admitted.

(* Invariant 3.6 *)
Lemma invariant36 : forall w (at_up : atomic_updates_rel w) 
  (t_u : ins_unique_f (txouts_calc (snd w))), 
  interIns (dom (change (snd w) t_u)) (dom (available w)) = nil.
Admitted.

(* Lemma 3.7 *)
Lemma lemma37 : forall w (at_up : atomic_updates_rel w), 
  incl (dom (available w)) (dom (fst w)).
Admitted.

(* Lemma 3.8 *)
Lemma lemma38 : forall w (at_up : atomic_updates_rel w) 
  (t_u : ins_unique_f (txouts_calc (snd w))), 
  interIns (dom (change (snd w) t_u)) (dom (fst w)) = nil.
Admitted.

(* Lemma 3.9.1 *)
Lemma lemma391 : forall w (at_up : atomic_updates_rel w) 
  (t_u : ins_unique_f (txouts_calc (snd w))) pf pf1, 
  UTxOeq (unionUTxO (change (snd w) t_u) (available w) pf) (total w t_u pf1).
Admitted.

(* Lemma 3.9.2 *)
Lemma lemma392 : forall w (at_up : atomic_updates_rel w) 
  (t_u : ins_unique_f (txouts_calc (snd w))) pf, 
  balance (change (snd w) t_u) + (balance (available w)) = balance (total w t_u pf).
Admitted.

(* never mind this stuff below *)

Lemma in_34 : forall t a b (w:Wallet) pf pf1, In t (dom (d_e (txins b) (unionUTxO (fst w) (r_r_ours (txouts b)) pf))) ->
In t (dom (d_e (txins (a :: b)) (unionUTxO (fst w) (r_r_ours (txouts (a :: b))) pf1))).
Proof.
  intros t a b w pf pf1 H. generalize UTxO_prop5.
  unfold UTxOeq. unfold UTxOinc. intros p5.
  unfold dom. eapply in_split. intros.
  apply p5. exact H0. generalize UTxO_prop12.
  unfold dom. intro u12. rewrite <- u12.
  unfold unionIns.
  unfold unionUTxO. apply in_dist.
  unfold unionUTxO in H.
  unfold dom in H. simpl in H. 
  assert (H0 : In t (fst (split (# (d_e (txins (b)) (r_r_ours (txouts (b))))))) \/
    In t (fst (split (# (d_e (txins (b)) (fst w)))))).
  Focus 2. inversion H0 as [H00 | H01].
  apply or_introl.
  unfold txouts. 
  destruct a as (li, lo). simpl. rewrite r_r_ours_dist.
  eapply in_split; try (exact H00); intros ab Hw.
  unfold d_e in p5. simpl in p5. 
  generalize (p5 (li++(txins b))) ()(r_r_ours (txouts b))). eapply p5.
  
In ab
  (d_e_fm
     (li ++ (fix txins (txs : Pow Tx) : Ins := match txs with
                                     | nil => nil
                                     | MkTx l _ :: xs => l ++ txins xs
                                     end) b)
     (r_r_ours_fm (makeUTxOforTx (MkTx li lo) lo) ++ r_r_ours_fm (txouts_calc b)))
 p5.
  apply p5.
  induction li. unfold makeUTxOforTx. simpl.
  assert 
  unfold unionIns in u12. rewrite <- u12 in H.
   rewrite in_dist.

(* Invariant 3.4 *)
Lemma pending_in_dom : forall w (at_up : atomic_updates_rel w), forall t, 
  In t (txins (snd w)) -> In t (dom (fst w)).
Proof.
  intros w ar t. intro H.
  induction ar; simpl; auto;

  unfold applyBlock; unfold updateUTxO; unfold updatePending;
  unfold applyBlock in H; unfold updateUTxO in H; unfold updatePending in H.
  simpl in H.
  induction b. unfold txins in H. inversion H.

  unfold txouts. unfold r_r_ours. simpl.
  unfold unionUTxO. unfold d_e. unfold dom. simpl.
  destruct a as (l,ls).
  unfold dom in IHb. simpl in IHb.
  rewrite r_r_ours_dist.
  eapply in_split. 

replace (d_e_fm (l ++ txins b) ((# (fst w)) ++ r_r_ours_fm (makeUTxOforTx (MkTx l ls) ls) ++ r_r_ours_fm (txouts_calc b))) with 
  ((d_e_fm (l ++ txins b) (# (fst w))) ++
    (d_e_fm (l ++ txins b) (r_r_ours_fm (makeUTxOforTx (MkTx l ls) ls) ++ r_r_ours_fm (txouts_calc b)))).


generalize UTxO_prop5.
  unfold UTxOeq; unfold d_e. unfold unionUTxO;
  unfold UTxOinc. simpl. 
  
 intros ab Hab.
Check in_split.
  eapply in_split.
  unfold r_r_ours_fm. unfold makeUTxOforTx.
  
  rewrite app_nil_r. unfold 
  destruct (in_dec decTx tx pending).

Focus 2.
  destruct w as (utxo, pending). simpl. simpl in H.
  induction pending. unfold available in precond. unfold ins_tx in precond.
  simpl in precond. destruct tx as (txi, txo). rewrite app_nil_r in H.
  rewrite d_e_nil in precond. unfold dom in precond.
  apply precond. auto.
  apply IHpending; auto. intros i ini.
  unfold available in precond. destruct a as (ai,ao).
  simpl in precond. induction ai.
  rewrite app_nil_l in precond.
  exact (precond i ini).
  apply IHai. destruct utxo.
  unfold d_e in precond. unfold dom in precond.
  simpl in precond.

Focus 2.
  
  unfold available. simpl.

induction w.


induction b; unfold updatePending. simpl.
  tauto.

  unfold applyBlock in H. simpl in H. destruct (in_dec decTx a (snd w)).

Focus 2. unfold updatePending in H.
  destruct (empty_inter (ins_tx a)). ; auto.

Focus 3.
 
  destruct a as (ai, ao).


Focus 3. simpl. destruct a as (i, o). destruct w as (u, p).
  simpl. unfold updatePending in H. 
  destruct (empty_inter (ins_tx tx) (txins b)).
  simpl in H. simpl in precond. simpl in pf. 
  simpl in IHb. simpl in n. clear IHar. 

nfold txouts_calc. simpl.

apply IHar. unfold newPending in H. simpl in H.
  destruct tx as (i,o). simpl in H.
  destruct (in_app_or i _ _ H) as [H1 | H2]; auto.
  unfold available in precond. unfold dom in precond.
  simpl in precond. generalize (precond t H1).
  destruct w as (u,p). simpl. intro Hde. 
  generalize (UTxO_prop_dom2 (txins p) u).
  unfold incl. unfold txins. simpl.
  intros Hinc Hpu. 
  apply (Hinc t Hpu).
   destruct tx as (i,o). simpl. simpl in H.
  destruct (in_app_or i _ _ H) as [H1 | H2]; intro Hit.
  generalize (UTxO_prop2_dom (txins (snd w)) (fst w)).
  unfold UTxOinc; unfold d_e. simpl. intro.
  unfold updatePending in H. simpl in precond.   

  unfold txouts_calc. unfold d_e_fm. simpl.
  generalize (#_eq_fst_sp t).
rewrite (#_eq_fst_sp t).
  
 unfold txins. simpl.
  Check ( (MkTx ai ao :: b)).
simpl.

  rewrite (#_eq_fst_sp t (d_e_fm (txins (MkTx ai ao :: b))
           (fst _ ++ r_r_ours_fm (txouts_calc (MkTx ai ao :: b))))).

simpl. unfold makeUTxOforTx. simpl.



  
  unfold d_e in precond. unfold d_e_fm in precond. 
  unfold dom in precond. simpl in precond. apply precond.
  generalize (precond t H). inversion H.

destruct (empty_inter (ins_tx a) match a with
                                | MkTx l _ => l ++ txins b
                                end).
  intros H. simpl.
  destruct w as (utxo, pending). unfold txins. simpl.

(* Lemma 3.2 *)
Lemma update_to_new : forall blockchain_u u b pf, UTxOeq (d_e (dom u) (updateUTxO blockchain_u b u pf)) (new blockchain_u b u).
Proof.
Admitted.

(* 
Definition unionUTxO (available w) (change (snd w))

(* subtraction lemma *)
Lemma subt_comp (a b c:nat) : (a + b = c -> a = c - b).
Proof.
  Admitted.
(*
  induction b.
(* case 0 *) replace (a+0) with a. 
  replace (c-0) with c. tauto. compute.
*)

Variable balance : UTxO -> Coin.


(* compute the sum of all coin values in a well-defined UTxO *)
Fixpoint sum_fm (f : UTxO) (f_wd : wd TxIn TxOut f) : nat :=
  match f_wd with
  | wd0 _ _ => 0
  | wd_new _ _ _ b f' wdf' _ => (snd b) + (sum_fm f' wdf')
  end.

(* define balance calculation for a UTxO presented as a list *)
Fixpoint coin_sum (utxo_list : list (TxIn*TxOut)) : Coin :=
  match utxo_list with 
  | nil => 0
  | u :: l => (snd (snd u)) + (coin_sum l)
  end.

Lemma sum_proof_ir : forall utxo f_wd f_wd', sum_fm utxo f_wd = sum_fm utxo f_wd'.
Proof.
  intros utxo f_wd f_wd'. 
  unfold sum_fm. induction f_wd. replace f_wd' with (wd0 TxIn TxOut). 
  auto. destruct f_wd'.
  compute in f_wd'. 
  assert (wd TxIn TxOut (null_fm TxIn TxOut)). exact (wd0 TxIn TxOut).

 induction f_wd'. auto. compute.

 (wd TxIn TxOut utxo).


(* any balance calculation for a utxo satisfying the balance_calc invariant property must coincide
  with the coin_sum balace calculation of this utxo presented as a list *)
Lemma coin_sum_balance :
  forall (utxo : UTxO) (l : list (TxIn*TxOut)) (f_wd : wd TxIn TxOut utxo), (forall t, utxo t <-> In t l) -> 
    coin_sum l = (sum_fm utxo f_wd).
Proof.
  intros utxo l f_wd H. induction l; simpl; simpl in H.  
(* empty wallet *) 
  unfold sum_fm. generalize f_wd. replace utxo with (null_fm TxIn TxOut).
  intro f_wd0. replace f_wd0 with (wd0 TxIn TxOut). auto.
  apply proof_irrelevance. 
  unfold wd.
  Check (wd0 _ _). 
  compute.
  unfold sum_fm. simpl. compute.
  auto. apply functional_extensionality.
  intro x. symmetry. apply prf_prop_ex. exact (H x).
(* a :: l wallet *)
  symmetry. apply balance_with_a. apply H. tauto.
Qed.

(* dependence *)
Definition depends (t2 t1 : Tx) :=  
  exists ix, (txins (fun t => t=t2)) (txid t1, ix).

(* set of independent transactions *)
Definition independednt (txs : Pow Tx) :=
  andPP' _ (txins txs) (dom (txouts txs)) = (fun t => False).


(* use property 2.6.1 as the invariant property defining balance *) 
Variable balance_calc :  (balance (fun u => False) = 0) /\
  (forall u v, (andPP' TxIn (dom u) (dom v) = (fun _ : TxIn => False) ->
  balance (orPP' (TxIn * TxOut) u v) = balance u + balance v)).


(* property 2.6.2 *)
Definition balance_prop2 (u : UTxO) (ins : Pow TxIn) :
  balance (d_e ins u) = (balance u) -(balance (d_r ins u)).
Proof.
  destruct balance_calc as [b0 b_c]. generalize (b_c (d_e ins u) (d_r ins u)).
  simpl. intro. apply subt_comp. rewrite <- H. 
  rewrite UTxO_prop10. auto.
  apply UTxO_prop11.
Qed.

(* UPDATING THE UTXO *)

(* assume the set of our addresses is constant *)
Variable ours : OurAddr.

(* add new outputs of a block to the UTxO *)
Definition new (b : Block) :=
  d_e (txins b) (r_r (txouts b) (OurOuts ours)).
  
(* update utxo to add new outputs of block b *)
Definition updateUTxO (b : Block) (utxo : UTxO) : UTxO :=
  d_e (txins b) (orPP' _ utxo (r_r (txouts b) (OurOuts ours))).


Lemma lemma32 : forall (b : Block) (u : UTxO),
  new b = d_e (dom u) (updateUTxO b u).
Proof.
  intros. unfold new. unfold updateUTxO. 
  unfold txins. unfold txouts. unfold OurOuts. 
  prove_prop. split; intros; split; try split; try split;
  try tauto. intro He.
  destruct H as [[[H0 H1] H1'] H2].

  Focus 2. destruct H as [[[H0 | H1] H1'] H2].
  destruct H2. exists (snd x). destruct x as [(x1,x2)]. simpl. auto.
  destruct H1'. destruct H1 as [[H01 H10] H02]. eexists. eexists. apply H01.
  destruct x as [(x1,x2)].
d exact H01.
exists (snd x). destruct x as [(x1,x2)]. simpl. auto.

 try tauto.
  split
