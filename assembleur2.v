Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import NPeano.

Import ListNotations.
(*-------------------Representation-Binaire-------------------------------------*)
(*ou reecrire fonction mod2 pour rendre que true ou false*)
(*Fixpoint nat_to_bool (n:nat) : bool :=
  match (n mod 2) with
  |0 => false
  |1 => true
  |(S p) => false (*theoreme pour prouver que ce cas narrive jamais*)
  end.*)
SearchAbout div.
SearchAbout pow S.

Fixpoint brem (n:nat) : bool :=
  if (beq_nat ((n/2)*2) n)
  then false
  else true.

(*
n: nat a encoder
SearchAbout()
k: encoder sur k bits
TODO: fonction decode : (list bool) -> nat
*)
Fixpoint encode (n:nat)(k:nat):(list bool):=
  match k with
  |0 => []
  |(S p) => (encode (n/2) p)++(brem n)::[]
  end.

Compute (encode 5 4).

(*-------------------Representation-Instructions--------------------------------*)
(*TODO:
-displacement: inter_code_car, eval_inter_code_car, instruction, decode_ins_icc
 *)


(*Representation dun code intermediaire qui va generer du binaire*)
Inductive inter_code_car : Type :=
|hexcar : nat -> inter_code_car (*generates 4-bit binary word*)
|constant: nat -> inter_code_car (*generates 4-bytes binary code*)
(*|displacement: nat -> inter_code_car*) (*generates 4-bytes binary code/ negative representation*)
.

(*evaluation of a inter_code_car*)
Fixpoint eval_inter_code_car (icc : inter_code_car) : (list bool) :=
  match icc with
  |(hexcar n) => (encode n 4)
  |(constant n) => (encode n 32)
  end.


(*hexadecimal is a list of inter_code_cars*)
(*Inductive type for register*)
(*1 register represented by 4 bits*)
Inductive reg: Type :=
|EAX: reg
|ECX: reg
|EDX: reg
|EBX: reg
|ESP: reg
|EBP: reg
|ESI: reg
|EDI: reg
|F : reg.


(*decode register*)
Fixpoint decode_reg (r : reg) : (list bool) :=
  match r with
  |EAX => (encode 0 4)
  |ECX => (encode 1 4)
  |EDX => (encode 2 4)
  |EBX => (encode 3 4)
  |ESP => (encode 4 4)
  |EBP => (encode 5 4)
  |ESI => (encode 6 4)
  |EDI => (encode 7 4)
  |F => (encode 15 4)
  end.


(*Operators represented by 1 byte*)
Inductive operator : Type :=
|ADD : operator
|SUB : operator
|AND : operator
|XOR : operator
.

(*decode operator to binary*)
Fixpoint decode_op (op: operator) : (list bool) :=
  match op with
  |ADD => (encode 6 4)++(encode 0 4)
  |SUB => (encode 6 4)++(encode 1 4)
  |AND => (encode 6 4)++(encode 2 4)
  |XOR => (encode 6 4)++(encode 3 4)
  end.

(*1 instruction represented by a maximum of 6 bytes*)
Inductive instruction: Type :=
|halt : instruction
|nop : instruction
|rrmovl : reg -> reg -> instruction
|irmovl : nat -> reg -> instruction
(*|rmmovl : reg -> constant -> reg -> instruction
|mrmovl : constant -> reg -> reg -> instruction*)
|opl : operator -> reg -> reg -> instruction
.


Fixpoint decode_ins (i : instruction) : (list bool) :=
  match i with
  |halt => (encode 0 4)++(encode 0 4)
  |nop => (encode 1 4)++(encode 0 4)
  |(rrmovl ra rb) => (encode 2 4)++(encode 0 4)++(decode_reg ra)++(decode_reg rb)
  |(irmovl n rb) => (encode 3 4)++(encode 0 4)++(encode 15 4)++(decode_reg rb)++(encode n 32)
  |(opl op ra rb) => (encode 6 4)++(decode_op op)++(decode_reg ra)++(decode_reg rb)
  end.

Compute (decode_ins halt).
Compute (decode_ins nop).
Compute (decode_ins (rrmovl EAX ECX)).
Compute (decode_ins (irmovl 15 EBX)).


(* ********************************************************************** *)
(*                              DECODE                                    *)
(* ********************************************************************** *)



Fixpoint decode (l : list bool) : (nat):=
  match l with
  | [] => 0
  | e::rest => match e with
         | false => decode rest
         | true => (decode rest) + (pow 2 ((length rest)))
         end
  end.


Compute (decode [false; true; true]).
Compute (decode [false;false;false;false;     false;true;false;true]).
(*SearchAbout not.
Lemma brem_S:forall n:nat, brem (S n)=negb ( brem n).
  intros.
  destruct n. reflexivity.
  SearchAbout plus S.
  simpl.
simpl.  
Lemma eq_div_brem:forall n, n / 2 * 2 + (if brem n then 1 else 0) = n.
  induction n. reflexivity.
  Opaque div.
  simpl. 
  
  SearchAbout   div .
intros n. *)

Lemma eq_encode_decod: forall k (n:nat), ((pow 2 k)>n)->(decode (encode n k))=n.
Proof.
  intros k.  
  induction k.
  - intros.
    simpl  in H.
    inversion H.
    + reflexivity.
    + inversion H1.
  - intros.
    Opaque div.
    simpl encode.
    assert (forall l l', decode (l++l') = (decode l) * pow 2 (length l') + decode l').
    { intros.
      induction l. simpl. reflexivity. case a. simpl.
      rewrite IHl. rewrite app_length.
      rewrite Nat.pow_add_r.
      rewrite mult_plus_distr_r. omega.
      simpl.
      rewrite IHl.
      reflexivity.
    (*  SearchAbout mult.
      replace (decode l * 2 ^ length l'+decode l'+ 2 ^ length (l ++ l'))
      with
      (decode l * 2 ^ length l'+ 2 ^ length (l ++ l')+decode l').
      
      replace
        (decode l * 2 ^ length l'+ 2 ^ length (l ++ l'))
        with
     ( (decode l + 2 ^ length l) * 2 ^ length l').
      reflexivity. 
       replace
        (decode l * 2 ^ length l'+ 2 ^ length (l ++ l'))
        with
     ( (decode l + 2 ^ length l) * 2 ^ length l').
       reflexivity.
        replace
        (decode l * 2 ^ length l'+ 2 ^ length (l ++ l'))
        with
     ( (decode l + 2 ^ length l) * 2 ^ length l').
       reflexivity.*)
       
    }
      rewrite H0 .
      rewrite IHk.
      simpl.
      induction n. simpl.  
       rewrite Nat.div_0_l. reflexivity.
       omega. simpl. rewrite <-Nat.add_1_l. SearchAbout plus div.
       assert(forall a b:nat,(a+b)/2=a/2+b/2).
       {
         induction a. simpl. reflexivity.  rewrite <-Nat.add_1_l.
         SearchAbout plus.
         rewrite plus_comm with (n:=1) (m:=a).
         intros b.
         rewrite <-plus_assoc with (n:=a) (m:=1) (p:=b).
         replace b with 0. simpl.  rewrite Nat.div_0_l.
         trivial. omega.  induction b. reflexivity. 
         rewrite<- IHb.
          admit.         
       }
       
      
       unfold brem.
       rewrite H1 with (a:=1) (b:=n).
       
       rewrite Nat.div_small with(a:=1)(b:=2). simpl.
 assert( 2 * (n / 2)<=n).
        {
          apply  Nat.mul_div_le with (b:=2)(a:=n). omega.
        }
        SearchAbout S .
        assert(n<S n). apply gt_Sn_n.
        
        SearchAbout (_<_).
        
        rewrite mult_comm with (n:=n/2) (m:=2).
        SearchAbout (_->_).
        assert( 2 * (n / 2)<S n).
        {
        apply le_lt_trans with (m:=n) (p:=S n) (n:=2*(n/2)).
        apply H2. apply H3.
        }
        apply Nat.lt_neq in H4. SearchAbout beq_nat.
         rewrite<- Nat.eqb_neq  with (x:=(2*(n/2))) (y:=(S n)) in H4.
         rewrite H4.
        
          
        }
        
       
        
        rewrite le_lt_trans with (m:=n) (p:=S n) (n:=2*(n/2)).
        admit.
      simpl in H.
      replace (2 ^ k + (2 ^ k + 0)) with (2 * (2 ^ k)) in H.
      SearchAbout lt div.
      assert (2 * 2 ^ k > 2* (n/2)).
      { assert( 2 * (n / 2)<=n).
        {
          apply  Nat.mul_div_le with (b:=2)(a:=n). omega.
        }
        SearchAbout (_>_).

        apply gt_le_trans with (n:=(2*2^k)) (m:=n) (p:=2*(n/2)).
        apply H.
        apply H1.
      }
      SearchAbout mult lt .
      apply Nat.mul_lt_mono_pos_l with (p:=2).
      apply lt_0_Sn.
      apply H1.
      omega.
Qed.

(*      SearchAbout lt.
      simpl.
      simpl
      * reflexivity.
      * admit.

    (*    n / 2 * 2 + (if brem n then 1 else 0) = n * a rpouver comm lemma*)

  induction n.
  - induction k; simpl.
    + auto.
    + assert (forall l l', decode (l++l') = (decode l) * pow 2 (length l') + decode l').
      { admit. }
      rewrite H0 .
      rewrite IHk.
      * reflexivity.
      * admit.
  - simpl.
    simpl  in H.
    inversion H.
    + reflexivity.
    + inversion H1.
  - Opaque div.
    simpl encode. 
(*
  
 Lemma eq_length: forall (n:nat) (k:nat),k > ... -> (length(encode n k))= k.
                                                  
Lemma eq_decod_encode: forall (l:list bool),(encode(decode l) (length l))=l.


*)
