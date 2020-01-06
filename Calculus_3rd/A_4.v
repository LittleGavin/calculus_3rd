Require Export A_3.
Require Import Rlogic.

(*F(x)的差商为f(x)的中值*)
Definition diff_quo_median F f a b :=
  forall u v, u ∈ [a,b] /\ v ∈ [a,b] /\ v-u>0 ->
  exists (p q:R), p ∈ [u,v] /\ q ∈ [u,v] /\ f p <= (F v - F u)/(v - u) <= f q.

Theorem Theorem4_1_1 : forall (S: R->R->R) (f F:R->R) (a b:R),
  integ_sys S f a b ->
  strict_unequal S f a b ->
  forall y, y ∈ [a,b] ->(forall x, x ∈ [a,b] -> F x = S y x) ->
  diff_quo_median F f a b.
Proof.
  intros.
  unfold diff_quo_median; intros.
  destruct H0 with (w1:=u)(w2:=v); auto.
  generalize (Valuation_Theorem S f F a b ); intros.
  apply H6 with (y:=y)(u:=u)(v:=v)in H; auto; clear H6.
  destruct H, H, H, H6.
  exists x, x0.
  split; auto. split; auto.
  destruct H3, H8, H7.
  split;
  apply Rmult_le_reg_r with (r:=v-u); auto;
  unfold Rdiv; rewrite Rinv_mult_rgt0 with (r:=(v-u))(r1:=F v - F u); auto.
Qed.


Theorem Theorem4_1_2 : forall (S: R->R->R) (f F:R->R) (a b:R),
  (forall u v, u ∈ [a,b] /\ v ∈ [a,b] -> S u v = F v - F u) ->
  diff_quo_median F f a b ->
  integ_sys S f a b /\ strict_unequal S f a b.
Proof.
 intros.
 unfold diff_quo_median in H0.
 split.
 - unfold integ_sys.
   split.
   + unfold additivity; intros.
     generalize (H w1 w2); intros; rewrite H2.
     generalize (H w2 w3); intros; rewrite H3.
     generalize (H w1 w3); intros; rewrite H4.
     ring. tauto. tauto. tauto.
   + unfold nonnegativity; intros.
     generalize H1; intro.
     apply H0 in H1; auto; clear H0.
     destruct H1, H0, H0, H1, H3.
     split; intros.
      * apply H5 in H0; clear H5.
        apply Rmult_le_reg_r with (r:=/(w2 - w1)).
        apply Rinv_0_lt_compat; tauto.
        rewrite Rinv_r_simpl_l. rewrite H.
        eapply Rle_trans. apply H0. apply H3. tauto.
        apply Rgt_not_eq; tauto.
      * apply H5 in H1; clear H5.
        apply Rmult_le_reg_r with (r:=/(w2 - w1)).
        apply Rinv_0_lt_compat; tauto.
        rewrite Rinv_r_simpl_l. rewrite H.
        eapply Rle_trans. apply H4. apply Rge_le; auto. tauto.
        apply Rgt_not_eq; tauto.
  - unfold strict_unequal; intros.
    generalize H2 as l; intro.
    apply H0 in H2; clear H0; rewrite H.
    destruct H2, H0, H0, H2, H3.
    split; intros.
    + apply Rmult_lt_reg_r with (r:= /(w2 - w1)).
      apply Rinv_0_lt_compat. tauto.
      rewrite Rinv_r_simpl_l.
      eapply Rlt_le_trans. apply H5. apply H0. auto.
      apply Rgt_not_eq; tauto.
    + apply Rmult_lt_reg_r with (r:= /(w2 - w1)).
      apply Rinv_0_lt_compat. tauto.
      rewrite Rinv_r_simpl_l.
      eapply Rle_lt_trans. apply H4. apply H5; auto.
      apply Rgt_not_eq; tauto.
    + tauto.
Qed.

(*定义4.2*)

(*可加性*)
Definition additivity' (S:R->R->R)(a b:R):=
  forall(u v w:R), u ∈ [a,b] /\ v ∈ [a,b] /\w ∈ [a,b] ->
  S u v + S v w = S u w. 

(*中值性*)
Definition median (S:R->R->R)(f:R->R)(a b:R):=
  forall(u v:R), u ∈ [a,b] /\ v ∈ [a,b] /\ v - u > 0 ->
  exists p q:R, p ∈ [u,v] /\ q ∈ [u,v] /\
  f p *(v - u)<=S u v<=f q *(v - u).

(*积分系统*)
Definition integ_sys' (S:R->R->R)(f:R->R)(a b:R) :=
  additivity' S a b /\ median S f a b.

Notation " S ∫ f '(x)dx' " := (integ_sys' S f)(at level 10).

(*可积*)
Definition integrable' f a b :=
  exists S, integ_sys' S f a b /\
  (forall S':R->R->R, integ_sys' S' f a b -> S' = S).

Definition F_f_i (f:R->R)(i n:nat)(x1 x2:R): R :=
  f(x1+(x2-x1)* INR(i+1) / INR(n+1)) - f(x1+(x2-x1)* INR i / INR(n+1)).

Open Scope nat_scope.
Fixpoint sum_f_N (f:R->R)(i n:nat) F (x1 x2:R) : R :=
  match i with
  | 0 => F f 0 n x1 x2
  | S p => sum_f_N f p n F x1 x2 + F f i n x1 x2
  end.

Open Scope R_scope.
Lemma asd : forall f u v i n ,
  sum_f_N f i n F_f_i u v = f (u+(v-u)*INR(i+1)/INR(n+1)) - f u.
Proof.
  intros.
  induction i.
  - unfold sum_f_N.  
    unfold F_f_i. simpl.
    rewrite Rmult_0_r. unfold Rdiv. rewrite Rmult_0_l. rewrite Rplus_0_r; auto.
  - assert(sum_f_N f (S i) n F_f_i u v =
           sum_f_N f i n F_f_i u v + F_f_i f (S i) n u v).
     { auto. }
    rewrite H. rewrite IHi.
    unfold F_f_i.
    unfold Rminus. 
    rewrite Rplus_comm. rewrite <- Rplus_assoc.
    apply Rplus_eq_compat_r.
    rewrite <- Nat.add_0_r with (n:= S i).
    rewrite Nat.add_succ_comm. ring.
Qed.

Lemma sum_N : forall f u v n, sum_f_N f n n F_f_i u v = f v - f u.
Proof.
  intros.
  rewrite asd.
  unfold Rdiv; rewrite Rinv_r_simpl_l.
  rewrite Rplus_minus; auto.
  apply not_0_INR.
  rewrite Nat.add_comm.
  apply Nat.neq_succ_0.
Qed.

Lemma not_exist' : forall {U: Type} (p: U->Prop), (~ exists x, p x ) ->
 ( forall x,  ~ p x ).
Proof.
  intros.
  unfold not; intro.
  unfold not in H. apply H. 
  exists x; auto.
Qed.


Lemma Rminus_Not_eq0 : forall a b, a<>b -> exists c, c>0 /\ c =Rabs(a - b).
Proof.
  intros.
  generalize (classic (exists c : R, c > 0 /\ c = Rabs (a - b))); intro.
  destruct H0; auto.
  apply not_exist' with(x:=Rabs (a - b)) in H0.
  destruct H0.
  split; auto.
  apply Rabs_pos_lt; apply Rminus_eq_contra; auto.
Qed.

Lemma lemma4_2_1 : forall F f a b, diff_quo_median F f a b ->
  forall u v, u ∈ [a,b] /\ v ∈ [a,b] /\ v - u > 0 ->
  forall i n:nat, (i<=n)%nat ->
  exists x1 x2, x1 ∈ [(u+(v-u)*INR i/INR(n+1)),(u+(v-u)*INR(i+1)/INR(n+1))] /\
                x2 ∈ [(u+(v-u)*INR i/INR(n+1)),(u+(v-u)*INR(i+1)/INR(n+1))] /\
                f x1 <= F_f_i F i n u v /((v-u)/INR(n+1)) <= f x2.
Proof.
  intros.
  unfold diff_quo_median in H.
  destruct H0, H2.
  assert((u+(v-u)*INR i/INR (n+1)) ∈ [a,b]).
   { unfold In; unfold cc.
     unfold In in H0, H2; unfold cc in H0, H2. destruct H0, H2, H4, H5.
     split; auto.
     apply Rplus_le_3_r.
     split.
     - apply Rle_trans with (r2:=a)(r3:=u); auto.
       unfold Rminus; rewrite Rplus_comm.
       apply Rplus_le_reg_r with (r:= -a).
       rewrite Rplus_assoc.
       repeat rewrite Rplus_opp_r.
       rewrite Rplus_0_r.
       apply Rplus_le_reg_r with (r:=(v + - u) * INR i / INR (n+1)).
       rewrite Rplus_opp_l. rewrite Rplus_0_l.
       repeat apply Rmult_le_pos. apply Rlt_le. tauto.
       apply pos_INR. apply Rlt_le. apply Rinv_0_lt_compat.
       apply lt_0_INR. rewrite Nat.add_comm. apply gt_Sn_O.
     - apply Rplus_le_reg_r with (r:= (v - u) * INR i / INR (n+1)).
       rewrite Rminus_plus_r.
       apply Rle_trans with (r2:=v)(r3:=b); auto.
       rewrite <- Rplus_minus with (r1:=u)(r2:=v) at 2.
       apply Rplus_le_compat_l.
       assert (INR i / INR(n+1) < 1).
        { apply Rmult_lt_reg_r with (r:=INR(n+1)).
          apply lt_0_INR. rewrite Nat.add_comm.
          apply gt_Sn_O. unfold Rdiv; rewrite Rinv_mult_rgt0.
          rewrite Rmult_1_l.
          apply lt_INR. rewrite Nat.add_comm. apply le_lt_n_Sm; auto.
          apply lt_0_INR; rewrite Nat.add_comm; apply gt_Sn_O. }
       rewrite <- Rmult_1_r with (r:=v-u) at 2.
       unfold Rdiv. rewrite Rmult_assoc.
       apply Rmult_le_compat_l. apply Rlt_le; auto.
       apply Rlt_le; auto.
   }
   assert((u+(v-u)*INR(i+1)/INR(n+1)) ∈ [a,b]).
   { unfold In; unfold cc.
     unfold In in H0, H2; unfold cc in H0, H2. destruct H0, H2, H4, H5, H6.
     split; auto.
     apply Rplus_le_3_r.
     split.
     - apply Rle_trans with (r2:=a)(r3:=u); auto.
       unfold Rminus; rewrite Rplus_comm.
       apply Rplus_le_reg_r with (r:= -a).
       rewrite Rplus_assoc.
       repeat rewrite Rplus_opp_r.
       rewrite Rplus_0_r.
       apply Rplus_le_reg_r with (r:=(v + - u) * INR (i+1) / INR (n+1)).
       rewrite Rplus_opp_l. rewrite Rplus_0_l.
       repeat apply Rmult_le_pos. apply Rlt_le. tauto.
       apply pos_INR. apply Rlt_le. apply Rinv_0_lt_compat.
       apply lt_0_INR. rewrite Nat.add_comm. apply gt_Sn_O.
     - apply Rplus_le_reg_r with (r:= (v-u)*INR(i+1)/INR(n+1)).
       rewrite Rminus_plus_r.
       apply Rle_trans with (r2:=v)(r3:=b); auto.
       rewrite <- Rplus_minus with (r1:=u)(r2:=v) at 2.
       apply Rplus_le_compat_l.
       assert (INR (i+1) / INR(n+1) <= 1).
        { apply Rmult_le_reg_r with (r:=INR (n+1)).
          apply lt_0_INR. rewrite Nat.add_comm.
          apply gt_Sn_O. unfold Rdiv; rewrite Rinv_mult_rgt0.
          rewrite Rmult_1_l.
          apply le_INR. apply Nat.add_le_mono_r; auto.
          rewrite Nat.add_comm.
          apply lt_0_INR; apply gt_Sn_O. 
        }
       rewrite <- Rmult_1_r with (r:=v-u) at 2.
       unfold Rdiv. rewrite Rmult_assoc.
       apply Rmult_le_compat_l; auto.
       apply Rlt_le; auto.
   }
   assert((u+(v-u)*INR(i+1)/INR(n+1))-(u+(v-u)*INR i/INR(n+1))>0).
   { apply Rgt_minus.
     apply Rplus_gt_compat_l.
     unfold Rdiv; repeat rewrite Rmult_assoc.
     apply Rmult_gt_compat_l; auto.
     apply Rmult_gt_compat_r; auto.
     apply Rinv_0_lt_compat.
     rewrite Nat.add_comm.
     apply lt_0_INR; apply gt_Sn_O.
     apply lt_INR.
     rewrite Nat.add_comm; apply Nat.lt_succ_diag_r. 
   }
   destruct H with (u:=(u + (v - u) * INR i / INR (n + 1)))
                   (v:=(u + (v - u) * INR (i + 1) / INR (n + 1))).
   split; tauto.
   destruct H7, H7, H8.
   exists x, x0.
   split; auto. split; auto.
   unfold F_f_i.
   assert(u+(v-u)*INR(i+1)/INR(n+1)-(u+(v-u)*INR i/INR(n+1)) = (v-u)/INR(n+1)).
    { assert (forall a b c d, a+b-(c+d)=(a-c)+(b-d)). { intros; ring. }
      rewrite H10. 
      assert (forall r, r-r=0). { intro; ring. }
      rewrite H11. rewrite Rplus_0_l.
      unfold Rdiv; repeat rewrite Rmult_assoc.
      rewrite <- Rmult_minus_distr_l with (r1:=v-u).
      unfold Rminus; rewrite Ropp_mult_distr_l.
      rewrite <- Rmult_plus_distr_r.  
      rewrite Nat.add_comm. rewrite S_O_plus_INR.
      rewrite Rplus_assoc; rewrite Rplus_opp_r; rewrite Rplus_0_r.
      rewrite Rmult_1_l; auto. }
    rewrite H10 in H9; auto.
Qed.


Definition f_x_i (f:R->R) (x:nat->R) i := f (x i).

Fixpoint sum_f_x_i (f:R->R)(n:nat) x : R :=
  match n with
  | 0 => f_x_i f x 0
  | S p => sum_f_x_i f p x + f_x_i f x n
  end.

Lemma th4_2_1 : forall F f a b,
  diff_quo_median F f a b -> uniform_continuous f a b ->
  forall s:R->R->R, (forall x y, s x y = F y - F x) ->
  integ_sys' s f a b.
Proof.
  intros.
  unfold diff_quo_median in H.
  unfold integ_sys'.
  split.
  - unfold additivity'; intros.
    repeat rewrite H1. ring.
  - unfold median; intros.
    generalize H2; intro.
    apply H in H2; clear H.
    destruct H2, H.
    exists x, x0.
    rewrite H1.
    split. tauto. split. tauto.
    eapply Rinv_le_r with (r:=v-u). tauto.
    unfold Rdiv; repeat rewrite Rinv_r_simpl_l.
    unfold Rdiv in H. tauto.
    apply Rgt_not_eq; tauto.
    apply Rgt_not_eq; tauto.
Qed.

Lemma th4_2_2 : forall F G f a b, diff_quo_median F f a b ->
  diff_quo_median G f a b -> uniform_continuous f a b ->
  forall u v, u ∈ [a,b] /\ v ∈ [a,b] /\ v-u>0 ->
  G v - G u = F v - F u.
Proof.
  intros.
  generalize ( classic (G v - G u = F v - F u) ); intros.
  destruct H3; auto.
  apply Rminus_Not_eq0 in H3.
  destruct H3, H3; rename x into c.
  unfold uniform_continuous in H1; destruct H1; rename x into d.
  
  assert(forall n:nat, 0 < (v - u) / INR (n + 1)) as minus_vu.
      { intro.
        unfold Rdiv; apply Rmult_lt_0_compat.
        apply Rgt_lt; tauto.
        apply Rinv_0_lt_compat; apply lt_0_INR.
        rewrite Nat.add_1_r; apply Nat.lt_0_succ. }
  
  assert(forall n, ((v - u) / INR (n + 1)) ∈ (0,(b - a)]) as In_vu.
      { intro.
        destruct H2, H5.
        unfold In in H2; unfold cc in H2.
        unfold In in H5; unfold cc in H5.
        unfold In; unfold oc.
        destruct H2, H5.
        split. apply Rlt_Rminus; auto.
        split; auto.
        apply Rle_trans with(r2:=v-u).
        rewrite <- Rmult_1_r with (r:=v-u) at 2.
        apply Rmult_le_compat_l; auto.
        apply Rlt_le; apply Rgt_lt; auto.
        rewrite <- Rinv_1. apply Rinv_le_contravar.
        apply Rlt_0_1. 
        generalize (le_INR 1 (n+1)); intro.
        simpl in H9; apply H9.
        rewrite Nat.add_1_r; apply le_n_S; apply Nat.le_0_l.
        unfold Rminus; apply Rplus_le_compat. tauto.
        apply Ropp_le_contravar; tauto. }
  
  assert(forall n:nat, c<=(v-u)*d((v-u)/ INR (n+1))).
   { intros.
     generalize (lemma4_2_1 F f a b H u v H2); intros.
     generalize (lemma4_2_1 G f a b H0 u v H2); intros.
     generalize (minus_vu n) as minus_vu_n; intro.
     generalize (In_vu n) as In_vu_n; intro.

     assert(forall x, x ∈ [u + (v - u) * INR 0 / INR (n + 1),
                           u + (v - u) * INR (0 + 1) / INR (n + 1)] ->
                      x ∈ [a,b]) as In_x.
      { intros.
        simpl in H7.
        rewrite Rmult_0_r in H7.
        unfold Rdiv in H7; rewrite Rmult_0_l in H7.
        rewrite Rplus_0_r in H7.
        rewrite Rmult_1_r in H7.
        unfold In in H7; unfold cc in H7.
        unfold In; unfold cc.
        destruct H7, H8.
        destruct H2; unfold In in H2; unfold cc in H2.
        destruct H2. split; auto.
        destruct H11. split.
        apply Rle_trans with (r2:=u); auto.
        apply Rle_trans with (r2:=u + (v - u) * / INR (n + 1)); auto.
        destruct H10; unfold In in H10; unfold cc in H10.
        destruct H10, H14.
        apply Rle_trans with (r2:=v); auto.
        rewrite <- Rplus_minus with(r1:=u)(r2:=v) at 2.
        apply Rplus_le_compat_l.
        rewrite <- Rmult_1_r with (r:=v-u) at 2.
        apply Rmult_le_compat_l with (r:=v-u).
        apply Rlt_le; auto.
        rewrite <- Rinv_1. apply Rinv_le_contravar.
        apply Rlt_0_1. 
        generalize (le_INR 1 (n+1)); intro.
        simpl in H16; apply H16.
        rewrite Nat.add_1_r; apply le_n_S; apply Nat.le_0_l. }

     assert(forall x (i:nat), (i<=n)%nat -> x ∈ [u+(v-u)*INR i/INR(n+1),
            u+(v-u)*INR(i+1)/INR(n+1)]->x ∈ [a,b]) as In_xi.
      { intros.
        unfold In in H8; unfold cc in H8.
        unfold In; unfold cc.
        destruct H8, H9.
        destruct H2; unfold In in H2; unfold cc in H2.
        destruct H2. split; auto.
        destruct H12. split.
        apply Rle_trans with (r2:=u); auto.
        apply Rplus_le_reg_pos_r with (r2:=(v-u)*INR i/INR(n+1)); auto.
        repeat apply Rmult_le_pos.
        apply Rge_le; apply Rgt_ge; tauto.
        apply pos_INR.
        apply Rlt_le; apply Rinv_0_lt_compat; apply lt_0_INR.
        rewrite Nat.add_1_r; apply Nat.lt_0_succ.
        apply Rle_trans with (r2:=u+(v-u) * INR(i+1)/INR(n+1)); auto.
        destruct H11; unfold In in H11; unfold cc in H11.
        destruct H11, H15.
        apply Rle_trans with (r2:=v); auto.
        rewrite <- Rplus_minus with(r1:=u)(r2:=v) at 2.
        apply Rplus_le_compat_l.
        rewrite <- Rmult_1_r with (r:=v-u) at 2.
        unfold Rdiv; rewrite Rmult_assoc.
        apply Rmult_le_compat_l with (r:=v-u).
        apply Rlt_le; auto.
        apply Rmult_le_reg_r with(r:=INR (n + 1)).
        apply lt_0_INR.
        rewrite Nat.add_1_r; apply Nat.lt_0_succ.
        rewrite Rmult_1_l.
        rewrite Rinv_mult_rgt0.
        repeat rewrite plus_INR; apply Rplus_le_compat_r.
        apply le_INR; auto.
        apply Rgt_lt; apply lt_0_INR.
        rewrite Nat.add_1_r; apply Nat.lt_0_succ. }

     assert(forall x1 x2, x1 ∈ [u+(v-u)*INR 0/INR(n+1),
       u+(v-u)*INR(0+1)/INR(n+1)] -> x2 ∈ [u+(v-u)*INR 0/INR(n+1),
       u+(v-u)*INR(0+1)/INR(n+1)] -> Rabs(x2-x1)<=(v-u)/INR(n+1)) as In_minus_x.
      { intros.
        simpl in H7, H8.
        rewrite Rmult_0_r in H7, H8.
        unfold Rdiv in H7, H8; rewrite Rmult_0_l in H7, H8.
        rewrite Rplus_0_r in H7, H8.
        rewrite Rmult_1_r in H7, H8.
        unfold In in H7, H8; unfold cc in H7, H8.
        destruct H7, H8.
        apply Rminus_Rabs with(a:=u)(b:=u + (v - u) * / INR (n + 1))
                              (r1:=x1) in H10; auto.
        rewrite <- Rabs_right with(r:=(v - u) / INR (n + 1)).
        rewrite Rplus_comm in H10.
        unfold Rminus in H10.
        rewrite Rplus_assoc in H10; rewrite Rplus_opp_r in H10.
        rewrite Rplus_0_r in H10. destruct H10; unfold Rminus; auto.
        rewrite Ropp_plus_distr in H10.
        rewrite <- Rplus_assoc in H10.
        rewrite Rplus_comm with(r1:=u) in H10; rewrite Rplus_assoc in H10.
        rewrite Rplus_opp_r in H10; rewrite Rplus_0_r in H10.
        rewrite Rabs_Ropp in H10; auto.
        apply Rgt_ge; auto. }

     assert(forall x1 x2 (i:nat), (i<=n)%nat -> x1 ∈ [u+(v-u)*INR i/INR(n+1),
       u+(v-u)*INR(i+1)/INR(n+1)] -> x2 ∈ [u+(v-u)*INR i/INR(n+1),
       u+(v-u)*INR(i+1)/INR(n+1)] ->Rabs(x2-x1)<=(v-u)/INR(n+1)) as In_minus_xi.
      { intros. unfold In in H8, H9; unfold cc in H8, H9.
        destruct H8, H9.
        apply Rminus_Rabs with(a:=u+(v-u)*INR i/INR(n+1))
                              (b:=u+(v-u)*INR(i+1)/INR(n+1))
                              (r1:=x1) in H11; auto.
        rewrite <- Rabs_right with(r:=(v - u) / INR (n + 1)).
        assert(forall a b c, a+b - (a+c) = b-c ). { intros; ring. }
        repeat rewrite H12 in H11. clear H12.
        unfold Rdiv in H11.
        assert(forall a b c d, a*b*c-a*d*c = (b-d)*a*c). { intros; ring. }
        repeat rewrite H12 in H11. clear H12.
        destruct H11.
        rewrite plus_comm in H11; rewrite plus_INR in H11.
        unfold Rminus in H11; rewrite Rplus_assoc in H11.
        rewrite Rplus_opp_r in H11; rewrite Rplus_0_r in H11.
        rewrite Rmult_1_l in H11.
        unfold Rminus; auto.
        unfold Rminus in H11. rewrite plus_INR in H11.
        rewrite Ropp_plus_distr in H11; rewrite <- Rplus_assoc in H11.
        rewrite Rplus_opp_r in H11; rewrite Rplus_0_l in H11.
        rewrite Rmult_assoc in H11.
        rewrite Rabs_mult with (x:=- INR 1 )in H11.
        rewrite Rabs_Ropp in H11. simpl in H11; rewrite Rabs_R1 in H11.
        rewrite Rmult_1_l in H11. unfold Rminus; auto.
        apply Rle_ge; apply Rlt_le; auto. }

     rewrite H4. repeat rewrite <- sum_N with (n:=n).
     assert(forall i:nat, (i<=n)%nat ->
       Rabs (sum_f_N G i n F_f_i u v - sum_f_N F i n F_f_i u v)<=
       ((v - u) / INR (n+1) * INR (i+1)) * d ((v - u) / INR (n+1))).
      { intros.
        induction i. 
        - simpl.
          generalize(H5 0%nat n H7); intros.
          generalize(H6 0%nat n H7); intros.
          destruct H8, H8. destruct H9, H9.
          destruct H8, H10, H9, H12.
          apply Rminus_Rabs with(a:= f x)(b:= f x0)
            (r1:=F_f_i F 0 n u v / ((v - u) / INR (n + 1))) in H13; auto.
          destruct H13.
          generalize (total_eq_or_neq (x2 - x) 0); intro.
          destruct H14.
          + apply Rminus_diag_uniq in H14; rewrite H14 in H13.
            rewrite Rminus_diag_eq with(r1:=f x) in H13; try reflexivity.
            rewrite Rabs_R0 in H13.
            apply Rle_antisym with(r1:=0) in H13; try apply Rabs_pos.
            rewrite <- Rdiv_minus_distr in H13.
            unfold Rdiv in H13; rewrite Rabs_mult in H13.
            apply eq_sym in H13; apply Rmult_integral in H13.
            destruct H13; apply Rlt_le.
            * rewrite H13.
              rewrite Rmult_1_r.
              apply Rmult_lt_0_compat; auto.
              destruct H1, H1.
              apply Rgt_lt; apply H1; auto.
            * apply Rinv_0_lt_compat in minus_vu_n.
              apply Rlt_not_eq in minus_vu_n.
              apply not_eq_sym in minus_vu_n; apply Rabs_pos_lt in minus_vu_n.
              apply Rlt_not_eq in minus_vu_n; apply not_eq_sym in minus_vu_n.
              unfold Rdiv in minus_vu_n; rewrite H13 in minus_vu_n.
              contradiction. 
          + assert(Rabs (f x2 - f x) <= d ((v - u) / INR (n + 1))).
             { apply Rle_trans with (r2:=d (Rabs (x2-x))).
               destruct H1, H15.
               rewrite <- Rplus_minus with(r1:=x)(r2:=x2) at 1.
               apply H16 with (x:=x) (h:=x2-x).
               rewrite Rplus_minus.
               split; try apply In_x; auto. 
               apply In_minus_x with(x1:=x) in H12; auto.
               destruct H12.
               destruct H1; unfold pos_inc in H1.
               destruct H1; apply H16; auto.
               * unfold In in In_vu_n; unfold oc in In_vu_n.
                 unfold In; unfold oc.
                 destruct In_vu_n; split; auto.
                 split. apply Rabs_pos_lt; auto.
                 apply Rlt_le; apply Rlt_le_trans with(r2:=(v-u)/INR(n+1));
                 tauto.
               * rewrite H12. apply Rle_refl. }
             apply Rle_trans with(r3:=d ((v - u) / INR (n + 1))) in H13; auto.
             rewrite Rmult_1_r.
             unfold Rdiv in H13; unfold Rdiv.
             rewrite Rmult_comm with(r1:=F_f_i G 0 n u v)
                                    (r2:=/ ((v - u) * / INR (n + 1))) in H13.
             rewrite Rmult_comm with(r1:=F_f_i F 0 n u v)
                                    (r2:=/ ((v - u) * / INR (n + 1))) in H13.
             rewrite <- Rmult_minus_distr_l in H13.
             rewrite Rabs_mult in H13.
             rewrite Rabs_right with (r:=/ ((v - u) * / INR (n + 1))) in H13.
             apply Rmult_le_compat_l with(r:=(v - u) * / INR (n + 1)) in H13.
             rewrite <- Rmult_assoc in H13.
             rewrite Rinv_r with(r:=(v - u) * / INR (n + 1)) in H13.
             rewrite Rmult_1_l in H13; auto.
             apply Rgt_not_eq; auto.
             apply Rlt_le; auto.
             apply Rle_ge; apply Rlt_le; apply Rinv_0_lt_compat; auto.
          +  generalize (total_eq_or_neq (x1 - x0) 0); intro.
             destruct H14.
             * apply Rminus_diag_uniq in H14; rewrite H14 in H13.
               rewrite Rminus_diag_eq with(r1:=f x0) in H13; try reflexivity.
               rewrite Rabs_R0 in H13.
               apply Rle_antisym with(r1:=0) in H13; try apply Rabs_pos.
               rewrite <- Rdiv_minus_distr in H13.
               unfold Rdiv in H13; rewrite Rabs_mult in H13.
               apply eq_sym in H13; apply Rmult_integral in H13.
               destruct H13; apply Rlt_le.
               -- rewrite H13.
                 rewrite Rmult_1_r.
                 apply Rmult_lt_0_compat; auto.
                 destruct H1, H1.
                 apply Rgt_lt; apply H1; auto.
               -- apply Rinv_0_lt_compat in minus_vu_n.
                 apply Rlt_not_eq in minus_vu_n.
                 apply not_eq_sym in minus_vu_n; apply Rabs_pos_lt in minus_vu_n.
                 apply Rlt_not_eq in minus_vu_n; apply not_eq_sym in minus_vu_n.
                 unfold Rdiv in minus_vu_n; rewrite H13 in minus_vu_n.
                 contradiction. 
             * assert(Rabs (f x1 - f x0) <= d ((v - u) / INR (n + 1))).
                { apply Rle_trans with (r2:=d (Rabs (x1-x0))).
                  destruct H1, H15.
                 rewrite <- Rplus_minus with(r1:=x0)(r2:=x1) at 1.
                 apply H16 with (x:=x0) (h:=x1-x0).
                 rewrite Rplus_minus.
                 split; try apply In_x; auto. 
                 apply In_minus_x with(x1:=x0) in H9; auto.
                 destruct H9.
                 destruct H1; unfold pos_inc in H1.
                 destruct H1; apply H16; auto.
                 - unfold In in In_vu_n; unfold oc in In_vu_n.
                   unfold In; unfold oc.
                   destruct In_vu_n; split; auto.
                   split. apply Rabs_pos_lt; auto.
                   apply Rlt_le; apply Rlt_le_trans with(r2:=(v-u)/INR(n+1));
                   tauto.
                 - rewrite H9; apply Rle_refl. }
               apply Rle_trans with(r3:=d ((v - u) / INR (n + 1))) in H13; auto.
               rewrite Rmult_1_r.
               unfold Rdiv in H13; unfold Rdiv.
               rewrite Rmult_comm with(r1:=F_f_i G 0 n u v)
                                      (r2:=/ ((v - u) * / INR (n + 1))) in H13.
               rewrite Rmult_comm with(r1:=F_f_i F 0 n u v)
                                      (r2:=/ ((v - u) * / INR (n + 1))) in H13.
               rewrite <- Rmult_minus_distr_l in H13.
               rewrite Rabs_mult in H13.
               rewrite Rabs_right with (r:=/ ((v - u) * / INR (n + 1))) in H13.
               apply Rmult_le_compat_l with(r:=(v - u) * / INR (n + 1)) in H13.
               rewrite <- Rmult_assoc in H13.
               rewrite Rinv_r with(r:=(v - u) * / INR (n + 1)) in H13.
               rewrite Rmult_1_l in H13; auto.
               apply Rgt_not_eq; auto.
               apply Rlt_le; auto.
               apply Rle_ge; apply Rlt_le; apply Rinv_0_lt_compat; auto.
    - generalize H7; intro.
      apply le_Sn_le in H7. apply IHi in H7. clear IHi.
      assert(sum_f_N G (S i) n F_f_i u v =
        F_f_i G (S i) n u v + sum_f_N G i n F_f_i u v ) as sumG_si_i.
       { unfold F_f_i at 2.
         repeat rewrite asd. 
         unfold Rminus. rewrite Rplus_assoc.
         rewrite Nat.add_1_r with(n:=i).
         rewrite <- Rplus_assoc with (r1:=-G(u+(v+-u)*INR(S i)/INR(n+1))).
         rewrite Rplus_opp_l; rewrite Rplus_0_l; auto. }
      assert(sum_f_N F (S i) n F_f_i u v =
        F_f_i F (S i) n u v + sum_f_N F i n F_f_i u v ) as sumF_si_i.
       { unfold F_f_i at 2.
         repeat rewrite asd. 
         unfold Rminus. rewrite Rplus_assoc.
         rewrite Nat.add_1_r with(n:=i).
         rewrite <- Rplus_assoc with (r1:=-F(u+(v+-u)*INR(S i)/INR(n+1))).
         rewrite Rplus_opp_l; rewrite Rplus_0_l; auto. }
      rewrite sumG_si_i; rewrite sumF_si_i.
      assert(forall a b c d, a+b-(c+d) = a-c + (b-d)). { intros; ring. }
      rewrite H9. clear H9.
      apply Rle_trans with (r2:=Rabs(F_f_i G (S i) n u v-F_f_i F (S i) n u v)+
        Rabs(sum_f_N G i n F_f_i u v-sum_f_N F i n F_f_i u v)).
      apply Rabs_triang. clear sumG_si_i. clear sumF_si_i.
      assert((v - u) / INR (n + 1) * INR (S i + 1) * d ((v - u) / INR (n + 1))=
             (v - u) / INR (n + 1) * d ((v - u) / INR (n + 1)) +
             (v - u) / INR (n + 1) * INR (i + 1) * d ((v - u) / INR (n + 1))).
       { rewrite plus_INR with(n:=S i). 
         rewrite Rplus_comm with (r1:=INR(S i)).
         rewrite Rmult_comm with(r2:=INR 1 + INR (S i)).
         repeat rewrite Rmult_plus_distr_r.
         rewrite Rmult_1_l.
         rewrite Rmult_comm with (r2:=INR (i + 1)).
         rewrite Nat.add_1_r with(n:=i); auto. }
      rewrite H9; apply Rplus_le_compat; auto. clear H9. clear H7.
      generalize (H5 (S i) n H8); intro.
      generalize (H6 (S i) n H8); intro. clear H5; clear H6.
      destruct H7, H5, H9, H6, H5, H7, H6, H10.
      apply Rminus_Rabs with(a:= f x)(b:= f x0)
            (r1:=F_f_i F (S i) n u v / ((v - u) / INR (n + 1))) in H11; auto.
      destruct H11.
      + generalize (total_eq_or_neq (x2 - x) 0); intro.
        destruct H12.
        * apply Rminus_diag_uniq in H12; rewrite H12 in H11.
          rewrite Rminus_diag_eq with(r1:=f x) in H11; try reflexivity.
          rewrite Rabs_R0 in H11.
          apply Rle_antisym with(r1:=0) in H11; try apply Rabs_pos.
          rewrite <- Rdiv_minus_distr in H11.
          unfold Rdiv in H11; rewrite Rabs_mult in H11.
          apply eq_sym in H11; apply Rmult_integral in H11.
          destruct H11; apply Rlt_le.
          -- rewrite H11.
             apply Rmult_lt_0_compat; auto.
             destruct H1, H1.
             apply Rgt_lt; apply H1; auto.
          -- apply Rinv_0_lt_compat in minus_vu_n.
             apply Rlt_not_eq in minus_vu_n.
             apply not_eq_sym in minus_vu_n; apply Rabs_pos_lt in minus_vu_n.
             apply Rlt_not_eq in minus_vu_n; apply not_eq_sym in minus_vu_n.
             unfold Rdiv in minus_vu_n; rewrite H11 in minus_vu_n.
             contradiction.
        * assert(Rabs (f x2 - f x) <= d ((v - u) / INR (n + 1))).
             { apply Rle_trans with (r2:=d (Rabs (x2-x))).
               destruct H1, H13.
               rewrite <- Rplus_minus with(r1:=x)(r2:=x2) at 1.
               apply H14 with (x:=x) (h:=x2-x).
               rewrite Rplus_minus.
               split; try apply In_xi with (i:=S i); auto.
               split; try apply In_xi with (i:=S i); auto.
               apply In_minus_xi with(x1:=x)(i:=S i) in H10; auto.
               destruct H10.
               destruct H1; unfold pos_inc in H1.
               destruct H1; apply H14; auto.
               - unfold In in In_vu_n; unfold oc in In_vu_n.
                 unfold In; unfold oc.
                 destruct In_vu_n; split; auto.
                 split. apply Rabs_pos_lt; auto.
                 apply Rlt_le; apply Rlt_le_trans with(r2:=(v-u)/INR(n+1));
                 tauto.
               - rewrite H10; apply Rle_refl. }
          apply Rle_trans with(r3:=d ((v - u) / INR (n + 1))) in H11; auto.
          unfold Rdiv in H11; unfold Rdiv.
          rewrite Rmult_comm with(r1:=F_f_i G (S i) n u v)
                                 (r2:=/ ((v - u) * / INR (n + 1))) in H11.
          rewrite Rmult_comm with(r1:=F_f_i F (S i) n u v)
                                 (r2:=/ ((v - u) * / INR (n + 1))) in H11.
          rewrite <- Rmult_minus_distr_l in H11.
          rewrite Rabs_mult in H11.
          rewrite Rabs_right with (r:=/ ((v - u) * / INR (n + 1))) in H11.
          apply Rmult_le_compat_l with(r:=(v - u) * / INR (n + 1)) in H11.
          rewrite <- Rmult_assoc in H11.
          rewrite Rinv_r with(r:=(v - u) * / INR (n + 1)) in H11.
          rewrite Rmult_1_l in H11; auto.
          apply Rgt_not_eq; auto.
          apply Rlt_le; auto.
          apply Rle_ge; apply Rlt_le; apply Rinv_0_lt_compat; auto.
     + generalize (total_eq_or_neq (x1 - x0) 0); intro.
        destruct H12.
        * apply Rminus_diag_uniq in H12; rewrite H12 in H11.
          rewrite Rminus_diag_eq with(r1:=f x0) in H11; try reflexivity.
          rewrite Rabs_R0 in H11.
          apply Rle_antisym with(r1:=0) in H11; try apply Rabs_pos.
          rewrite <- Rdiv_minus_distr in H11.
          unfold Rdiv in H11; rewrite Rabs_mult in H11.
          apply eq_sym in H11; apply Rmult_integral in H11.
          destruct H11; apply Rlt_le.
          -- rewrite H11.
             apply Rmult_lt_0_compat; auto.
             destruct H1, H1.
             apply Rgt_lt; apply H1; auto.
          -- apply Rinv_0_lt_compat in minus_vu_n.
             apply Rlt_not_eq in minus_vu_n.
             apply not_eq_sym in minus_vu_n; apply Rabs_pos_lt in minus_vu_n.
             apply Rlt_not_eq in minus_vu_n; apply not_eq_sym in minus_vu_n.
             unfold Rdiv in minus_vu_n; rewrite H11 in minus_vu_n.
             contradiction.
        * assert(Rabs (f x1 - f x0) <= d ((v - u) / INR (n + 1))).
             { apply Rle_trans with (r2:=d (Rabs (x1-x0))).
               destruct H1, H13.
               rewrite <- Rplus_minus with(r1:=x0)(r2:=x1) at 1.
               apply H14 with (x:=x0) (h:=x1-x0).
               rewrite Rplus_minus.
               split; try apply In_xi with (i:=S i); auto.
               split; try apply In_xi with (i:=S i); auto.
               apply In_minus_xi with(x1:=x0)(i:=S i) in H6; auto.
               destruct H6.
               destruct H1; unfold pos_inc in H1.
               destruct H1; apply H14; auto.
               - unfold In in In_vu_n; unfold oc in In_vu_n.
                 unfold In; unfold oc.
                 destruct In_vu_n; split; auto.
                 split. apply Rabs_pos_lt; auto.
                 apply Rlt_le; apply Rlt_le_trans with(r2:=(v-u)/INR(n+1));
                 tauto.
               - rewrite H6; apply Rle_refl. }
          apply Rle_trans with(r3:=d ((v - u) / INR (n + 1))) in H11; auto.
          unfold Rdiv in H11; unfold Rdiv.
          rewrite Rmult_comm with(r1:=F_f_i G (S i) n u v)
                                 (r2:=/ ((v - u) * / INR (n + 1))) in H11.
          rewrite Rmult_comm with(r1:=F_f_i F (S i) n u v)
                                 (r2:=/ ((v - u) * / INR (n + 1))) in H11.
          rewrite <- Rmult_minus_distr_l in H11.
          rewrite Rabs_mult in H11.
          rewrite Rabs_right with (r:=/ ((v - u) * / INR (n + 1))) in H11.
          apply Rmult_le_compat_l with(r:=(v - u) * / INR (n + 1)) in H11.
          rewrite <- Rmult_assoc in H11.
          rewrite Rinv_r with(r:=(v - u) * / INR (n + 1)) in H11.
          rewrite Rmult_1_l in H11; auto.
          apply Rgt_not_eq; auto.
          apply Rlt_le; auto.
          apply Rle_ge; apply Rlt_le; apply Rinv_0_lt_compat; auto. }
    generalize(Nat.le_refl n); intro.
    apply H7 in H8.
    unfold Rdiv in H8.
    rewrite Rinv_mult_rgt0 in H8; auto.
    apply lt_0_INR.
    rewrite Nat.add_1_r; apply Nat.lt_0_succ. }
    
  destruct H1, H6.
  unfold pos_inc in H1; unfold bounded_rec_f in H6.
  destruct H1.
  assert((v-u)/c>0).
   { unfold Rdiv.
     apply Rmult_gt_0_compat. tauto.
     apply Rlt_gt; apply Rinv_0_lt_compat; auto. }
  apply H6 in H9.
  destruct H9, H9.
  generalize H9 as In_someone; intro.
  apply H1 in H9.
  unfold Rdiv in H10; rewrite Rmult_1_l in H10.
  rewrite Rabs_Rinv in H10; try apply Rgt_not_eq; auto.
  rewrite Rabs_right in H10; try apply Rgt_ge; auto.
  apply Rmult_lt_compat_r with(r:=c) in H10; auto.
  rewrite Rinv_mult_rgt0 in H10; auto.
  rewrite Rmult_comm in H10.
  apply Rmult_lt_compat_r with(r:=d x) in H10; auto.
  rewrite Rinv_mult_rgt0 in H10; auto.
  assert(exists n:nat, (v - u) / INR (n + 1) < x). 
   { generalize (classic (exists n:nat, (v - u) / INR (n + 1) < x)); intro.
     destruct H11; auto.
     generalize (not_not_archimedean ((v-u)/x-1)); intro.
     destruct H12; intro.
     apply not_exist' with (x:=n)
       (p:= (fun n:nat =>(v - u) / INR (n + 1) < x)) in H11.
     apply not_Rlt in H11.
     unfold In in In_someone; unfold oc in In_someone.
     destruct In_someone, H13.
     apply Rmult_ge_compat_l with (r:=/x) in H11;
     try apply Rgt_ge; try apply Rinv_0_lt_compat; auto.
     rewrite Rinv_l in H11; try apply Rgt_not_eq; auto.
     apply Rmult_ge_compat_r with (r:=INR(n+1)) in H11.
     rewrite Rmult_1_l in H11.
     unfold Rdiv in H11.
     rewrite <- Rmult_assoc in H11. rewrite Rinv_mult_rgt0 in H11.
     rewrite Rmult_comm in H11; rewrite plus_INR in H11.
     apply Rplus_ge_compat_r with(r:=-1) in H11.
     rewrite Rplus_assoc in H11;
     rewrite Rplus_opp_r in H11; rewrite Rplus_0_r in H11.
     apply Rge_le; auto.
     apply lt_0_INR; apply Nat.add_pos_r; apply Nat.lt_0_1.
     apply Rle_ge; apply pos_INR. }
  destruct H11.
  apply H8 in H11; try apply In_vu; auto.
  apply Rmult_le_compat_l with(r:=v-u) in H11.
  generalize (H5 x0); intro.
  apply Rle_trans with(r1:=c) in H11; auto.
  apply Rlt_not_ge in H10.
  apply Rle_ge in H11; contradiction.
  apply Rlt_le; tauto.
Qed.

Theorem Theorem4_2 : forall F f a b,
  diff_quo_median F f a b -> uniform_continuous f a b ->
  integ_sys' (fun u v => F v-F u) f a b /\
  (forall G, diff_quo_median G f a b ->
  forall u v, u ∈ [a,b] /\ v ∈ [a,b] /\ v-u>0 ->
  G v - G u = F v - F u).
Proof.
  intros.
  split.
  - apply th4_2_1 with (F:=F); auto.
  - intros.
    apply th4_2_2 with (f:=f)(a:=a)(b:=b); auto.
Qed.

Lemma lemma4_3_1 : forall  r r1 r2, r<=r1 -> r1<=r2 ->
  Rabs r1 <= Rabs r \/ Rabs r1 <= Rabs r2.
Proof.
  intros.
  generalize (total_order_T r1 0); intro.
  destruct H1. destruct s.
  - cut (Rabs r1 <= Rabs r); auto.
    apply Ropp_le_contravar in H.
    apply Rsqr_incr_1 in H. repeat rewrite <- Rsqr_neg in H.
    apply Rsqr_le_abs_0; auto.
    apply Ropp_0_ge_le_contravar; apply Rgt_ge; auto.
    apply Rle_trans with (r2:= -r1); auto.
    apply Ropp_0_ge_le_contravar; apply Rgt_ge; auto.
  - rewrite e; rewrite Rabs_R0.
    generalize (Rabs_pos r); intro; auto.
  - cut (Rabs r1 <= Rabs r2); auto.
    apply Rsqr_le_abs_0. apply Rsqr_incr_1 in H0; auto.
    apply Rlt_le; auto.
    apply Rle_trans with (r2:=r1); auto.
    apply Rlt_le; auto.
Qed.


(* 若F在[a,b]上强可导，f(x)是F(x)的导数，则在[a,b]上有两点u、v，使得
  f(u)(b-a)>=F(b)-F(a)>=f(v)(b-a) *)

Lemma lemma4_3_2 : forall F f a b, a<b -> str_derivative F f a b ->
  exists u v, u ∈ [a,b] /\ v ∈ [a,b] /\
              f u*(b-a)<= F b -F a <= f v * (b - a).
Proof.
Admitted.

Theorem Theorem4_3 : forall F f a b,
  diff_quo_median F f a b /\
  (exists M, M>0 /\ forall x h, x ∈ [a,b] /\ (x+h) ∈ [a,b] ->
  Rabs(f(x+h) - f(x)) <= M*(Rabs h))
  <-> str_derivative F f a b.
Proof.
  intros.
  unfold diff_quo_median; unfold str_derivative.
  split.
  - intros.
    destruct H, H0, H0. rename x into M.
    exists M.
    split; auto; intros.
    generalize ( total_order_T h 0); intro.
    destruct H3. destruct s.
    + destruct H with (u:=x+h)(v:=x).
      unfold Rminus; rewrite Ropp_plus_distr; rewrite <- Rplus_assoc.
      rewrite Rplus_opp_r; rewrite Rplus_0_l.
      generalize (Ropp_gt_lt_0_contravar h r); intro.
      split; tauto. destruct H3, H3, H4, H5.
      apply Rplus_le_compat_r with (r:=-f x)in H5.
      apply Rplus_le_compat_r with (r:=-f x)in H6.
      generalize (H1 x (x0-x)); intro.
      generalize (H1 x (x1-x)); intro.
      repeat rewrite Rplus_minus in H7.
      repeat rewrite Rplus_minus in H8.
      destruct H2.
      assert (x ∈ [a,b] /\ x0 ∈ [a,b]).
       { split; auto.
         unfold In; unfold cc.
         unfold In in H2, H3, H9; unfold cc in H2, H3, H9.
         destruct H2, H3, H9. split; auto.
         split.
         apply Rle_trans with(r2:=x+h); tauto.
         apply Rle_trans with (r2:=x); tauto. }
      assert (x ∈ [a,b] /\ x1 ∈ [a,b]).
       { split; auto.
         unfold In; unfold cc.
         unfold In in H2, H4, H9; unfold cc in H2, H4, H9.
         destruct H2, H4, H9. split; auto.
         split.
         apply Rle_trans with(r2:=x+h); tauto.
         apply Rle_trans with (r2:=x); tauto. }
      assert(Rabs((F x-F(x+h))/(x-(x+h))+-f x) <= Rabs(f x0 + - f x) \/
        Rabs((F x-F(x+h))/(x-(x+h))+-f x) <= Rabs(f x1+-f x)).
       { apply lemma4_3_1; auto. }
      apply H7 in H10; apply H8 in H11.
      destruct H12.
      * assert(h<>0) as l. { apply Rlt_not_eq; auto. }
        assert(Rabs((F x-F(x+h))/(x-(x+h))+-f x)<=M*Rabs(x0-x)).
         { apply Rle_trans with (r2:=Rabs (f x0 - f x)); auto. }
        unfold Rminus in H13. rewrite Ropp_plus_distr in H13;
        rewrite <- Rplus_assoc in H13.
        rewrite Rplus_opp_r in H13; rewrite Rplus_0_l in H13.
        unfold Rdiv in H13. rewrite <- Ropp_inv_permute in H13; auto.
        rewrite <- Ropp_mult_distr_r in H13; rewrite Ropp_mult_distr_l in H13.
        rewrite Ropp_plus_distr in H13; rewrite Ropp_involutive in H13.
        rewrite <- pow2_abs; rewrite <- Rsqr_pow2; unfold Rsqr.
        apply Rmult_le_reg_r with (r:=Rabs (/h)).
        apply Rabs_pos_lt; apply Rinv_neq_0_compat; apply Rlt_not_eq; auto.
        repeat rewrite Rmult_assoc;
        repeat rewrite <- Rabs_mult; rewrite Rinv_r; auto; rewrite Rmult_1_r.
        unfold Rminus. rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
        rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r;
        rewrite Rplus_comm with(r1:=F(x+h)).
        apply Rle_trans with (r2:=M*Rabs (x0 + - x)); auto.
        apply Rmult_le_compat_l. apply Rlt_le; auto.
        unfold In in H2; unfold cc in H2; destruct H2.
        repeat rewrite Rabs_left1.
        apply Ropp_le_contravar; apply Rplus_le_reg_r with (r:=x).
        rewrite Rplus_assoc; rewrite Rplus_opp_l;
        rewrite Rplus_0_r; rewrite Rplus_comm.
        unfold In in H3; unfold cc in H3. tauto.
        apply Rlt_le; auto.
        apply Rplus_le_reg_r with (r:=x).
        rewrite Rplus_assoc; rewrite Rplus_opp_l;
        rewrite Rplus_0_r; rewrite Rplus_comm.
        rewrite Rplus_0_r.
        unfold In in H3; unfold cc in H3; tauto.
      * assert(h<>0) as l. { apply Rlt_not_eq; auto. }
        assert(Rabs((F x-F(x+h))/(x-(x+h))+-f x)<=M*Rabs(x1-x)).
        { apply Rle_trans with (r2:=Rabs (f x1 - f x)); auto. }
        unfold Rminus in H13.
        rewrite Ropp_plus_distr in H13; rewrite <- Rplus_assoc in H13.
        rewrite Rplus_opp_r in H13; rewrite Rplus_0_l in H13.
        unfold Rdiv in H13. rewrite <- Ropp_inv_permute in H13; auto.
        rewrite <- Ropp_mult_distr_r in H13; rewrite Ropp_mult_distr_l in H13.
        rewrite Ropp_plus_distr in H13; rewrite Ropp_involutive in H13.
        rewrite <- pow2_abs; rewrite <- Rsqr_pow2; unfold Rsqr.
        apply Rmult_le_reg_r with (r:=Rabs (/h)).
        apply Rabs_pos_lt; apply Rinv_neq_0_compat; apply Rlt_not_eq; auto.
        repeat rewrite Rmult_assoc; repeat rewrite <- Rabs_mult;
        rewrite Rinv_r; auto; rewrite Rmult_1_r.
        unfold Rminus. rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
        rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r;
        rewrite Rplus_comm with(r1:=F(x+h)).
        apply Rle_trans with (r2:=M*Rabs (x1 + - x)); auto.
        apply Rmult_le_compat_l. apply Rlt_le; auto.
        unfold In in H2; unfold cc in H2; destruct H2.
        repeat rewrite Rabs_left1.
        apply Ropp_le_contravar; apply Rplus_le_reg_r with (r:=x).
        rewrite Rplus_assoc; rewrite Rplus_opp_l;
        rewrite Rplus_0_r; rewrite Rplus_comm.
        unfold In in H4; unfold cc in H4. tauto.
        apply Rlt_le; auto.
        apply Rplus_le_reg_r with (r:=x).
        rewrite Rplus_assoc; rewrite Rplus_opp_l;
        rewrite Rplus_0_r; rewrite Rplus_comm.
        rewrite Rplus_0_r.
        unfold In in H4; unfold cc in H4; tauto.
   + rewrite e.
     rewrite Rplus_0_r; rewrite Rmult_0_r; rewrite Rminus_0_r; rewrite Rminus_diag_eq; auto.
     rewrite <- Rsqr_pow2; rewrite Rsqr_0; rewrite Rmult_0_r; rewrite Rabs_R0;
     apply Req_le_sym; auto.
   + destruct H2. destruct H with (u:=x)(v:=x+h).
     rewrite <- R_distr; rewrite Rminus_diag_eq; auto; rewrite Rplus_0_l.
     split; auto.
     destruct H4, H4, H5, H6.
     apply Rplus_le_compat_r with (r:=-f x)in H6.
     apply Rplus_le_compat_r with (r:=-f x)in H7.
     generalize (H1 x (x0-x)); intro.
     generalize (H1 x (x1-x)); intro.
     repeat rewrite Rplus_minus in H8.
     repeat rewrite Rplus_minus in H9.
     assert (x ∈ [a,b] /\ x0 ∈ [a,b]).
      { split; auto.
        unfold In; unfold cc.
        unfold In in H2, H3, H4; unfold cc in H2, H3, H4.
        destruct H2, H3, H4. split; auto.
        split.
        apply Rle_trans with(r2:=x); tauto.
        apply Rle_trans with (r2:=x+h); tauto. }
     assert (x ∈ [a,b] /\ x1 ∈ [a,b]).
      { split; auto.
        unfold In; unfold cc.
        unfold In in H2, H3, H5; unfold cc in H2, H3, H5.
        destruct H2, H3, H5. split; auto.
        split.
        apply Rle_trans with(r2:=x); tauto.
        apply Rle_trans with (r2:=x+h); tauto. }
     assert(Rabs ((F(x+h)-F x)/((x+h)-x)+-f x)<=Rabs(f x0+-f x) \/
            Rabs ((F(x+h)-F x)/((x+h)-x)+-f x)<=Rabs(f x1+-f x)).
      { apply lemma4_3_1; auto. }
     apply H8 in H10; apply H9 in H11.
     destruct H12.
     * assert(h<>0) as l. { apply Rgt_not_eq; auto. }
       assert(Rabs ((F(x+h)-F x)/((x+h)-x)+-f x)<=M*Rabs(x0-x)).
        { apply Rle_trans with (r2:=Rabs (f x0 - f x)); auto. }
       rewrite <- R_distr in H13.
       rewrite Rminus_diag_eq with (r1:=x)(r2:=x)in H13; auto;
       rewrite Rplus_0_l in H13.
       rewrite <- pow2_abs; rewrite <- Rsqr_pow2; unfold Rsqr.
       apply Rmult_le_reg_r with (r:=Rabs (/h)).
       apply Rabs_pos_lt; apply Rinv_neq_0_compat; apply Rgt_not_eq; auto.
       repeat rewrite Rmult_assoc; repeat rewrite <- Rabs_mult;
       rewrite Rinv_r; auto;
       rewrite Rmult_1_r.
       unfold Rminus. rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
       rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
       unfold Rminus in H13; apply Rle_trans with (r2:=M*Rabs (x0 + - x)); auto.
       apply Rmult_le_compat_l. apply Rlt_le; auto.
       unfold In in H4; unfold cc in H4; destruct H4.
       repeat rewrite Rabs_right.
       apply Rplus_le_reg_r with (r:=x).
       rewrite Rplus_assoc; rewrite Rplus_opp_l;
       rewrite Rplus_0_r; rewrite Rplus_comm. tauto.
       apply Rgt_ge; auto.
       apply Rplus_ge_reg_l with (r:=x).
       rewrite Rplus_0_r. rewrite Rplus_comm; rewrite Rplus_assoc.
       rewrite Rplus_opp_l; rewrite Rplus_0_r. apply Rle_ge; tauto.
     * assert(h<>0) as l. { apply Rgt_not_eq; auto. }
       assert(Rabs ((F(x+h)-F x)/((x+h)-x)+-f x)<=M*Rabs(x1-x)).
        { apply Rle_trans with (r2:=Rabs (f x1 - f x)); auto. }
       rewrite <- R_distr in H13.
       rewrite Rminus_diag_eq with (r1:=x)(r2:=x)in H13; auto;
       rewrite Rplus_0_l in H13.
       rewrite <- pow2_abs; rewrite <- Rsqr_pow2; unfold Rsqr.
       apply Rmult_le_reg_r with (r:=Rabs (/h)).
       apply Rabs_pos_lt; apply Rinv_neq_0_compat; apply Rgt_not_eq; auto.
       repeat rewrite Rmult_assoc; repeat rewrite <- Rabs_mult;
       rewrite Rinv_r; auto; rewrite Rmult_1_r.
       unfold Rminus. rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
       rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
       unfold Rminus in H13; apply Rle_trans with (r2:=M*Rabs (x1 + - x)); auto.
       apply Rmult_le_compat_l. apply Rlt_le; auto.
       unfold In in H5; unfold cc in H5; destruct H5.
       repeat rewrite Rabs_right.
       apply Rplus_le_reg_r with (r:=x).
       rewrite Rplus_assoc; rewrite Rplus_opp_l;
       rewrite Rplus_0_r; rewrite Rplus_comm. tauto.
       apply Rgt_ge; auto.
       apply Rplus_ge_reg_l with (r:=x).
       rewrite Rplus_0_r. rewrite Rplus_comm; rewrite Rplus_assoc.
       rewrite Rplus_opp_l; rewrite Rplus_0_r. apply Rle_ge; tauto.
  - split; intros.
    destruct H, H. rename x into M.
    + assert(str_derivative F f u v).
       { unfold str_derivative; intros.
         exists M; split; auto.
         intros.
         assert(x ∈ [a,b] /\ (x + h) ∈ [a,b]).
          { unfold In; unfold cc.
            destruct H0, H3, H2.
            unfold In in H0, H3, H2, H5; unfold cc in H0, H3, H2, H5.
            destruct H0, H3, H2, H5.
            repeat split; auto.
            apply Rle_trans with (r2:=u); tauto.
            apply Rle_trans with (r2:=v); tauto.
            apply Rle_trans with (r2:=u); tauto.
            apply Rle_trans with (r2:=v); tauto. }
         apply H1 in H3; auto. }
      apply lemma4_3_2 in H2.
      destruct H2, H2, H2, H3.
      exists x, x0; split; auto. split; auto.
      apply Rinv_le_r with (r:=(v-u)) in H4.
      assert (v - u <> 0). { apply Rgt_not_eq; tauto. }
      unfold Rdiv in H4; rewrite Rinv_r_simpl_l in H4;
      rewrite Rinv_r_simpl_l in H4; auto.
      tauto.
      apply Rgt_lt; apply Rminus_gt; tauto.
    + destruct H, H. rename x into M.
      exists (2*M).
      split. apply Rmult_lt_0_compat; auto. apply Rlt_0_2.
      intros.
      generalize (H0 (x+h) (-h)); intro.
      assert((x+h) ∈ [a,b] /\ x ∈ [a,b]). { split; tauto. }
      rewrite Rplus_assoc in H2; rewrite Rplus_opp_r in H2;
      rewrite Rplus_0_r in H2.
      apply H0 in H1; apply H2 in H3. clear H2.
      rewrite <- Rsqr_pow2 in H3; rewrite <- Rsqr_neg in H3;
      rewrite <- Rsqr_pow2 in H1.
      apply Rplus_le_compat with (r1:=Rabs (F x - F (x + h) - f (x + h) * - h))
                                 (r2:=M * h²) in H1; auto.
      generalize(Rabs_triang (F x-F(x+h)-f(x+h)*-h)(F(x+h)-F x-f x*h)); intro.
      apply Rle_trans with (r3:=M * h² + M * h²) in H2; auto.
      rewrite <- plus_ab_minus_cd in H2. rewrite Rplus_comm with(r1:=F x) in H2.
      rewrite Rminus_diag_eq with (r1:=F (x + h) + F x)in H2; auto.
      rewrite Rminus_0_l in H2; rewrite Ropp_plus_distr in H2.
      rewrite Ropp_mult_distr_l in H2; rewrite Rmult_opp_opp in H2.
      rewrite Ropp_mult_distr_l in H2.
      repeat rewrite <- Rmult_plus_distr_r in H2.
      rewrite Rsqr_abs in H2; unfold Rsqr in H2; rewrite <- Rmult_assoc in H2.
      rewrite Rabs_mult in H2. rewrite double.
      generalize(Rabs_pos h); intro.
      destruct H4.
      * apply Rmult_le_reg_r with(r:=Rabs h); auto.
      * rewrite <- Rabs_R0 in H4; apply Rsqr_eq_asb_1 in H4;
        rewrite Rsqr_0 in H4.
        apply eq_sym in H4. apply Rsqr_eq_0 in H4.
        rewrite H4; rewrite Rplus_0_r. rewrite Rabs_R0; rewrite Rmult_0_r.
        rewrite Rminus_diag_eq; auto. rewrite Rabs_R0. apply Req_le_sym; auto.
Qed.


Lemma lemma4_4_2 : forall F f a b, derivative F f a b ->
  exists u v, u ∈ [a,b] /\ v ∈ [a,b] /\ f u*(b-a)<=F b-F a <=f v *(b-a).
Proof.
Admitted.


(* 若 F 在[a , b] 上一致可导, f(x)是 F(x)的导数,则在[ a , b] 上有两点 u、v ,使得
     f(u)*(b-a)<=F(b)-F(a)<=f(v)*(b-a) *)

Lemma lemma4_4_1 : forall F f a b, derivative F f a b ->
  forall u v , u ∈ [a,b] /\ v ∈ [a,b] /\ v-u>0 -> derivative F f u v.
Proof.
  intros.
  unfold derivative; unfold derivative in H.
  destruct H. rename x into d.
  destruct H, H1, H2, H2. rename x into M.
  exists d.
  assert (forall z, z ∈ (0, v - u] -> z ∈ (0, b - a]).
   { intros.
     unfold In; unfold oc; unfold In in H4; unfold oc in H4.
     destruct H0.
     unfold In in H0; unfold cc in H0.
     destruct H0, H6, H5, H5, H9, H4, H11.
     repeat split; auto.
     apply Rlt_Rminus; auto.
     apply Rle_trans with(r2:=v - u); auto.
     unfold Rminus; apply Rplus_le_compat. tauto.
     apply Ropp_le_contravar; tauto. }
  assert((v - u) ∈ (0, v - u]) as l1.
   { unfold In; unfold oc.
      repeat split; try apply Rgt_lt; try tauto.
      apply Rge_refl. }
  split.
  - unfold pos_inc; unfold pos_inc in H.
    split.
    + intros.
      apply H4 in H5. apply H; auto.
    + intros.
      apply H4 in H5; apply H4 in H6.
      apply H; auto.
  - split.
    + unfold bounded_rec_f; unfold bounded_rec_f in H1.
      intros.
      apply H1 in H5.
      destruct H5.
      assert(x ∈ (0, b - a] -> x ∈ (0, v - u] \/ x ∈ (v - u, b - a]).
       { intro.
         unfold In; unfold oc.
         generalize (classic (0 < x <= v - u)); intro.
         destruct H7.
         left. split; try apply Rgt_lt; auto. tauto.
         right. apply not_and_or in H7.
         unfold In in H6; unfold oc in H6.
         destruct H6, H8, H7. contradiction.
         apply Rnot_le_lt in H7.
         repeat split; auto.
         apply Rlt_le_trans with(r2:=x); auto. }
      destruct H5; generalize H5 as l2; intro; apply H6 in H5; destruct H5.
      exists x; split; auto.
      exists (v-u); split; auto.
      unfold pos_inc in H; destruct H.
      destruct H5, H9.
      apply H8 in H9; auto.
      apply H4 in l1; apply H in l1.
      apply H in l2.
      apply Rlt_le_trans with (r2:=Rabs (1 / d x)); auto.
      unfold Rdiv. repeat rewrite Rmult_1_l.
      repeat rewrite Rabs_pos_eq.
      apply Rle_Rinv; auto.
      apply Rlt_le; apply Rinv_0_lt_compat; auto.
      apply Rlt_le; apply Rinv_0_lt_compat; auto.
    + exists M; split; auto.
      intros.
      assert(forall x, x ∈ [u, v] -> x ∈ [a, b]).
       { intros.
         unfold In; unfold cc; unfold In in H6; unfold cc in H6.
         destruct H0, H7.
         unfold In in H0, H7; unfold cc in H0, H7.
         destruct H0, H9, H7, H11, H6, H13.
         repeat split; auto.
         apply Rle_trans with(r2:=u); auto.
         apply Rle_trans with(r2:=v); auto. }
      apply H3.
      destruct H5, H7.
      apply H6 in H5; apply H6 in H7.
      split; auto.
Qed.


Theorem Theorem4_4 : forall F f a b, derivative F f a b <->
  diff_quo_median F f a b /\ uniform_continuous f a b.
Proof.
  intros.
  split; intros.
  - split.
    + unfold diff_quo_median; intros.
      apply lemma4_4_1 with (u:=u)(v:=v)in H; auto.
      apply lemma4_4_2 in H.
      destruct H, H, H, H1.
      exists x, x0. split; auto. split; auto.
      apply Rmult_le_r with (r:=(v-u)). tauto.
      unfold Rdiv; rewrite Rinv_mult_rgt0; auto; tauto.
    + unfold derivative in H; unfold uniform_continuous.
      destruct H, H, H0, H1, H1. rename x into d; rename x0 into M.
      exists (mult_real_f (2*M) d).
      assert(0<2*M) as l. { apply Rmult_gt_0_compat; auto. apply Rlt_0_2. }
      split.
       * unfold pos_inc; unfold pos_inc in H. 
         destruct H; split; intros.
         apply H in H4; unfold mult_real_f.
         apply Rmult_gt_0_compat; auto.
         unfold mult_real_f.
         apply (H3 z1) in H5; auto.
         apply (Rmult_le_compat_l (2*M)); auto.
         apply Rlt_le; auto.
       * split.
         -- unfold bounded_rec_f; unfold mult_real_f; intros.
            unfold bounded_rec_f in H0.
            destruct H0 with (M:=2*M*M0).
            unfold Rdiv; apply Rmult_gt_0_compat; auto. 
            destruct H4. exists x. split; auto.
            apply (Rmult_lt_reg_l (2*M)); auto.
            rewrite <- Rabs_right with(r:=2*M) at 2.
            rewrite <- Rabs_mult.
            assert(2*M<>0). { apply Rgt_not_eq; auto. }
            unfold Rdiv; rewrite Rinv_mult_distr; auto. rewrite Rmult_1_l.
            rewrite <- Rmult_assoc; rewrite Rinv_r; auto.
            unfold pos_inc in H. destruct H. apply H in H4.
            apply Rgt_not_eq; auto.
            apply Rgt_ge; auto.
         -- intros.
            assert(h<>0) as p. { tauto. }
            assert((x+h) ∈ [a,b] /\ x ∈ [a,b] /\ -h <> 0).
             { split. tauto. split. tauto. apply Ropp_neq_0_compat; tauto. }
            apply H2 in H3.
            generalize(H2 (x+h) (-h)); intro.
            rewrite Rplus_assoc in H5; rewrite Rplus_opp_r in H5;
            rewrite Rplus_0_r in H5.
            apply H5 in H4; clear H5.
            rewrite Rabs_Ropp in H4.
            apply Rplus_le_compat with (r1:=Rabs (F x-F(x+h)-f(x+h)*-h))
                                 (r2:=M*Rabs h * d (Rabs h)) in H3; auto.
            generalize(Rabs_triang (F x-F(x+h)-f(x+h)*-h)(F(x+h)-F x-f x*h));
            intro.
            rewrite <- double in H3.
            apply Rle_trans with (r3:=2 * (M * Rabs h * d (Rabs h))) in H5; auto.
            rewrite <- plus_ab_minus_cd in H5.
            rewrite Rplus_comm with(r1:=F x) in H5.
            rewrite Rminus_diag_eq with (r1:=F (x + h) + F x)in H5; auto.
            rewrite Rminus_0_l in H5; rewrite Ropp_plus_distr in H5.
            rewrite Ropp_mult_distr_l in H5; rewrite Rmult_opp_opp in H5.
            rewrite Ropp_mult_distr_l in H5;
            repeat rewrite <- Rmult_plus_distr_r in H5.
            rewrite Rabs_mult in H5.
            rewrite Rmult_assoc in H5.
            rewrite (Rmult_comm (Rabs h)(d(Rabs h))) in H5.
            repeat rewrite <- Rmult_assoc in H5.  
            unfold mult_real_f.
            generalize(Rabs_pos h); intro.
            destruct H6.
            apply Rmult_le_reg_r with(r:=Rabs h); auto.
            rewrite <- Rabs_R0 in H6; apply Rsqr_eq_asb_1 in H6;
            rewrite Rsqr_0 in H6.
            apply eq_sym in H6.  apply Rsqr_eq_0 in H6. destruct p; auto.
  - destruct H.
    unfold diff_quo_median in H; unfold uniform_continuous in H0.
    unfold derivative.
    destruct H0, H0, H1. rename x into d.
    exists d. split; auto. split; auto.
    exists 1. split. apply Rlt_0_1. intros.
    rewrite Rmult_1_l.
    assert(h<0\/h>0) as l.
     { apply Rdichotomy; tauto. }
    destruct H3, H4, l.
    assert((x+h) ∈ [a,b]/\ x ∈ [a,b] /\ x-(x+h)>0).
     { split; auto. split; auto.
       unfold Rminus; rewrite Ropp_plus_distr.
       rewrite <- Rplus_assoc; rewrite Rplus_opp_r.
       rewrite Rplus_0_l. apply Ropp_gt_lt_0_contravar; auto. }
    apply H in H7.
    destruct H7, H7, H7, H8, H9.
    apply Rplus_le_compat_r with (r:=-f x)in H9.
    apply Rplus_le_compat_r with (r:=-f x)in H10.
    generalize (Req_dec x0 x); intro.
    destruct H11.
    + generalize (Req_dec x1 x); intro.
      destruct H12.
      * rewrite H11 in H9; rewrite H12 in H10.
        rewrite Rplus_opp_r in H9. rewrite Rplus_opp_r in H10.
        apply Rle_antisym in H9; auto.
        unfold Rminus in H9; rewrite Ropp_plus_distr in H9.
        rewrite <- Rplus_assoc in H9; rewrite Rplus_opp_r in H9.
        rewrite Rplus_0_l in H9.
        unfold Rdiv in H9; rewrite <- Ropp_inv_permute in H9; auto.
        rewrite <- Ropp_mult_distr_r in H9; rewrite Ropp_mult_distr_l in H9.
        rewrite Ropp_plus_distr in H9; rewrite Ropp_involutive in H9.
        rewrite Rplus_comm with(r1:=-F x) in H9.
        apply Rmult_eq_compat_r with(r:=h) in H9.
        rewrite Rmult_plus_distr_r in H9; rewrite Rmult_0_l in H9.
        rewrite Rmult_assoc in H9; rewrite Rinv_l in H9; auto.
        rewrite Rmult_1_r in H9.
        unfold Rminus; rewrite Ropp_mult_distr_l; rewrite H9.
        rewrite Rabs_R0.
        apply Rmult_le_pos. apply Rabs_pos.
        unfold pos_inc in H0; destruct H0.
        apply Rlt_le; apply H0.
        unfold In; unfold oc.
        unfold In in H3, H4; unfold cc in H3, H4.
        destruct H3, H4.
        split. apply Rlt_Rminus; auto.
        split. apply Rabs_pos_lt; auto.
        rewrite Rabs_left; auto.
        apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
        rewrite Rplus_comm; apply Rplus_le_reg_r with (r:=h).
        rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r.
        destruct H14, H15.
        apply Rle_trans with(r2:=x+h); auto.
        apply Rplus_le_compat_r; auto.
      * rewrite H11 in H9; rewrite Rplus_opp_r in H9.
        assert (x ∈ [a,b] /\ (x+(x1-x)) ∈ [a,b] /\ x1-x<>0).
         { split; auto.
           split.
           unfold In; unfold cc.
           unfold In in H3, H4, H8; unfold cc in H3, H4, H8.
           destruct H3, H4, H8. split; auto.
           rewrite Rplus_minus. split.
           apply Rle_trans with(r2:=x+h); tauto.
           apply Rle_trans with (r2:=x); tauto.
           apply Rminus_eq_contra; auto. }
        apply H2 in H13. generalize H9; intro.
        apply Rle_trans with(r3:= f x1 + - f x) in H9; auto.
        rewrite <- Rabs_right in H10.
        rewrite <- Rabs_right with(r:=(F x-F(x+h))/(x-(x+h))+-f x) in H10.
        unfold Rminus in H10; rewrite Ropp_plus_distr in H10.
        rewrite <- Rplus_assoc in H10; rewrite Rplus_opp_r in H10.
        rewrite Rplus_0_l in H10.
        unfold Rdiv in H10; rewrite <- Ropp_inv_permute in H10; auto.
        rewrite <- Ropp_mult_distr_r in H10; rewrite Ropp_mult_distr_l in H10.
        rewrite Ropp_plus_distr in H10; rewrite Ropp_involutive in H10.
        rewrite Rplus_comm with(r1:=-F x) in H10.
        rewrite Rplus_minus in H13.
        apply Rle_trans with (r3:=d (Rabs (x1 - x))) in H10; auto.
        apply Rmult_le_reg_r with (r:=Rabs (/h)).
        apply Rabs_pos_lt; apply Rinv_neq_0_compat; apply Rlt_not_eq; auto.
        rewrite Rmult_comm with(r1:=Rabs h); rewrite Rmult_assoc.
        repeat rewrite <- Rabs_mult; rewrite Rinv_r; auto. 
        rewrite Rabs_R1; rewrite Rmult_1_r.
        unfold Rminus. rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
        rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
        apply Rle_trans with(r2:=d (Rabs (x1 - x))); auto.
        unfold pos_inc in H0; destruct H0.
        assert((Rabs(x1-x)) ∈ (0,b-a]/\(Rabs h) ∈ (0,b-a]/\Rabs(x1-x)<=Rabs h).
         { split; unfold In; unfold oc.
           unfold In in H3, H4, H8; unfold cc in H3, H4, H8.
           destruct H3, H4, H8.
           split. apply Rlt_Rminus; auto.
           split. apply Rabs_pos_lt; apply Rminus_eq_contra; auto.
           rewrite Rabs_left1. rewrite Ropp_minus_distr.
           unfold Rminus; apply Rplus_le_compat. tauto.
           apply Ropp_le_contravar; apply Rle_trans with(r2:=x+h); tauto.
           apply Rle_minus; tauto.
           unfold In in H3, H4; unfold cc in H3, H4.
           destruct H3, H4.
           split.
           split. apply Rlt_Rminus; auto.
           split. apply Rabs_pos_lt; auto.
           rewrite Rabs_left; auto.
           apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
           rewrite Rplus_comm; apply Rplus_le_reg_r with (r:=h).
           rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r.
           destruct H16, H17.
           apply Rle_trans with(r2:=x+h); auto.
           apply Rplus_le_compat_r; auto.
           unfold In in H8; unfold cc in H8. destruct H8.
           rewrite Rabs_left1. rewrite Rabs_left; auto.
           apply Ropp_le_contravar. apply Rplus_le_reg_r with(r:=x).
           rewrite Rminus_plus_r; rewrite Rplus_comm; tauto.
           apply Rle_minus; tauto. }
        destruct H16, H17, H18.
        apply H15 in H18; auto.
        right; rewrite H18; auto.
        apply Rle_ge; auto. apply Rle_ge; auto.
    + generalize (Req_dec x1 x); intro.
      destruct H12.
      * rewrite H12 in H10; rewrite Rplus_opp_r in H10.
        assert (x ∈ [a,b] /\ (x+(x0-x)) ∈ [a,b] /\ x0-x<>0).
         { split; auto.
           split.
           unfold In; unfold cc.
           unfold In in H3, H4, H7; unfold cc in H3, H4, H7.
           destruct H3, H4, H8. split; auto.
           rewrite Rplus_minus. split.
           apply Rle_trans with(r2:=x+h); tauto.
           apply Rle_trans with (r2:=x); tauto.
           apply Rminus_eq_contra; auto. }
        apply H2 in H13. generalize H9; intro.
        apply Rle_trans with(r3:= 0) in H9; auto.
        rewrite <- Ropp_involutive with(r:=f x0 + - f x) in H14.
        rewrite <- Rabs_right with(r:=-(f x0 + - f x)) in H14.
        rewrite <- Ropp_involutive with(r:=(F x-F(x+h))/(x-(x+h))+-f x) in H14.
        rewrite <- Rabs_right with(r:=-((F x-F(x+h))/(x-(x+h))+-f x)) in H14.
        apply Ropp_le_cancel in H14.
        repeat rewrite Rabs_Ropp in H14.
        unfold Rminus in H14; rewrite Ropp_plus_distr in H14.
        rewrite <- Rplus_assoc in H14; rewrite Rplus_opp_r in H14.
        rewrite Rplus_0_l in H14.
        unfold Rdiv in H14; rewrite <- Ropp_inv_permute in H14; auto.
        rewrite <- Ropp_mult_distr_r in H14; rewrite Ropp_mult_distr_l in H14.
        rewrite Ropp_plus_distr in H14; rewrite Ropp_involutive in H14.
        rewrite Rplus_comm with(r1:=-F x) in H14.
        rewrite Rplus_minus in H13.
        apply Rle_trans with (r3:=d (Rabs (x0 - x))) in H14; auto.
        apply Rmult_le_reg_r with (r:=Rabs (/h)).
        apply Rabs_pos_lt; apply Rinv_neq_0_compat; apply Rlt_not_eq; auto.
        rewrite Rmult_comm with(r1:=Rabs h); rewrite Rmult_assoc.
        repeat rewrite <- Rabs_mult; rewrite Rinv_r; auto. 
        rewrite Rabs_R1; rewrite Rmult_1_r.
        unfold Rminus. rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
        rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
        apply Rle_trans with(r2:=d (Rabs (x0 - x))); auto.
        unfold pos_inc in H0; destruct H0.
        assert((Rabs(x0-x)) ∈ (0,b-a]/\(Rabs h) ∈ (0,b-a]/\Rabs(x0-x)<=Rabs h).
         { split; unfold In; unfold oc.
           unfold In in H3, H4, H7; unfold cc in H3, H4, H7.
           destruct H3, H4, H7.
           split. apply Rlt_Rminus; auto.
           split. apply Rabs_pos_lt; apply Rminus_eq_contra; auto.
           rewrite Rabs_left1. rewrite Ropp_minus_distr.
           unfold Rminus; apply Rplus_le_compat. tauto.
           apply Ropp_le_contravar; apply Rle_trans with(r2:=x+h); tauto.
           apply Rle_minus; tauto.
           unfold In in H3, H4; unfold cc in H3, H4.
           destruct H3, H4.
           split.
           split. apply Rlt_Rminus; auto.
           split. apply Rabs_pos_lt; auto.
           rewrite Rabs_left; auto.
           apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
           rewrite Rplus_comm; apply Rplus_le_reg_r with (r:=h).
           rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r.
           destruct H16, H17.
           apply Rle_trans with(r2:=x+h); auto.
           apply Rplus_le_compat_r; auto.
           unfold In in H7; unfold cc in H7. destruct H7.
           rewrite Rabs_left1. rewrite Rabs_left; auto.
           apply Ropp_le_contravar. apply Rplus_le_reg_r with(r:=x).
           rewrite Rminus_plus_r; rewrite Rplus_comm; tauto.
           apply Rle_minus; tauto. }
        destruct H16, H17, H18.
        apply H15 in H18; auto.
        right; rewrite H18; auto.
        rewrite <- Ropp_0; apply Ropp_le_ge_contravar; auto.
        rewrite <- Ropp_0; apply Ropp_le_ge_contravar; auto.
      * assert (x ∈ [a,b] /\ (x+(x1-x)) ∈ [a, b] /\ x1-x<>0).
         { split; auto.
           split.
           unfold In; unfold cc.
           unfold In in H3, H4, H8; unfold cc in H3, H4, H8.
           destruct H3, H4, H8. split; auto.
           rewrite Rplus_minus. split.
           apply Rle_trans with(r2:=x+h); tauto.
           apply Rle_trans with (r2:=x); tauto.
           apply Rminus_eq_contra; auto. }
         assert (x ∈ [a,b] /\ (x+(x0-x)) ∈ [a,b] /\ x0-x<>0).
         { split; auto.
           split.
           unfold In; unfold cc.
           unfold In in H3, H4, H7; unfold cc in H3, H4, H7.
           destruct H3, H4, H8. split; auto.
           rewrite Rplus_minus. split.
           apply Rle_trans with(r2:=x+h); tauto.
           apply Rle_trans with (r2:=x); tauto.
           apply Rminus_eq_contra; auto. }
         apply H2 in H13; apply H2 in H14.
         apply lemma4_3_1 with(r:=f x0 + - f x) in H10; auto.
         destruct H10.
         -- unfold Rminus in H10; rewrite Ropp_plus_distr in H10.
            rewrite <- Rplus_assoc in H10; rewrite Rplus_opp_r in H10.
            rewrite Rplus_0_l in H10.
            unfold Rdiv in H10; rewrite <- Ropp_inv_permute in H10; auto.
            rewrite <- Ropp_mult_distr_r in H10;
            rewrite Ropp_mult_distr_l in H10.
            rewrite Ropp_plus_distr in H10; rewrite Ropp_involutive in H10.
            rewrite Rplus_comm with(r1:=-F x) in H10.
            rewrite Rplus_minus in H14.
            apply Rle_trans with (r3:=d (Rabs (x0 - x))) in H10; auto.
            apply Rmult_le_reg_r with (r:=Rabs (/h)).
            apply Rabs_pos_lt; apply Rinv_neq_0_compat; apply Rlt_not_eq; auto.
            rewrite Rmult_comm with(r1:=Rabs h); rewrite Rmult_assoc.
            repeat rewrite <- Rabs_mult; rewrite Rinv_r; auto. 
            rewrite Rabs_R1; rewrite Rmult_1_r.
            unfold Rminus. rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
            rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
            apply Rle_trans with(r2:=d (Rabs (x0 - x))); auto.
            unfold pos_inc in H0; destruct H0.
            assert((Rabs (x0 - x)) ∈ (0,b-a]/\(Rabs h) ∈ (0,b-a]/\
                   Rabs (x0 - x)<=Rabs h).
             { split; unfold In; unfold oc.
               unfold In in H3, H4, H7; unfold cc in H3, H4, H7.
               destruct H3, H4, H7.
               split. apply Rlt_Rminus; auto.
               split. apply Rabs_pos_lt; apply Rminus_eq_contra; auto.
               rewrite Rabs_left1. rewrite Ropp_minus_distr.
               unfold Rminus; apply Rplus_le_compat. tauto.
               apply Ropp_le_contravar; apply Rle_trans with(r2:=x+h); tauto.
               apply Rle_minus; tauto.
               unfold In in H3, H4; unfold cc in H3, H4.
               destruct H3, H4.
               split.
               split. apply Rlt_Rminus; auto.
               split. apply Rabs_pos_lt; auto.
               rewrite Rabs_left; auto.
               apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
               rewrite Rplus_comm; apply Rplus_le_reg_r with (r:=h).
               rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r.
               destruct H16, H17.
               apply Rle_trans with(r2:=x+h); auto.
               apply Rplus_le_compat_r; auto.
               unfold In in H7; unfold cc in H7. destruct H7.
               rewrite Rabs_left1. rewrite Rabs_left; auto.
               apply Ropp_le_contravar. apply Rplus_le_reg_r with(r:=x).
               rewrite Rminus_plus_r; rewrite Rplus_comm; tauto.
               apply Rle_minus; tauto. }
            destruct H16, H17, H18.
            apply H15 in H18; auto.
            right; rewrite H18; auto.
         -- unfold Rminus in H10; rewrite Ropp_plus_distr in H10.
            rewrite <- Rplus_assoc in H10; rewrite Rplus_opp_r in H10.
            rewrite Rplus_0_l in H10.
            unfold Rdiv in H10; rewrite <- Ropp_inv_permute in H10; auto.
            rewrite <- Ropp_mult_distr_r in H10;
            rewrite Ropp_mult_distr_l in H10.
            rewrite Ropp_plus_distr in H10; rewrite Ropp_involutive in H10.
            rewrite Rplus_comm with(r1:=-F x) in H10.
            rewrite Rplus_minus in H13.
            apply Rle_trans with (r3:=d (Rabs (x1 - x))) in H10; auto.
            apply Rmult_le_reg_r with (r:=Rabs (/h)).
            apply Rabs_pos_lt; apply Rinv_neq_0_compat; apply Rlt_not_eq; auto.
            rewrite Rmult_comm with(r1:=Rabs h); rewrite Rmult_assoc.
            repeat rewrite <- Rabs_mult; rewrite Rinv_r; auto. 
            rewrite Rabs_R1; rewrite Rmult_1_r.
            unfold Rminus. rewrite Rmult_plus_distr_r;
            rewrite Ropp_mult_distr_l.
            rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
            apply Rle_trans with(r2:=d (Rabs (x1 - x))); auto.
            unfold pos_inc in H0; destruct H0.
            assert((Rabs (x1 - x)) ∈ (0,b-a]/\(Rabs h) ∈ (0,b-a]/\
                   Rabs (x1 - x)<=Rabs h).
            { split; unfold In; unfold oc.
              unfold In in H3, H4, H8; unfold cc in H3, H4, H8.
              destruct H3, H4, H8.
              split. apply Rlt_Rminus; auto.
              split. apply Rabs_pos_lt; apply Rminus_eq_contra; auto.
              rewrite Rabs_left1. rewrite Ropp_minus_distr.
              unfold Rminus; apply Rplus_le_compat. tauto.
              apply Ropp_le_contravar; apply Rle_trans with(r2:=x+h); tauto.
              apply Rle_minus; tauto.
              unfold In in H3, H4; unfold cc in H3, H4.
              destruct H3, H4.
              split.
              split. apply Rlt_Rminus; auto.
              split. apply Rabs_pos_lt; auto.
              rewrite Rabs_left; auto.
              apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
              rewrite Rplus_comm; apply Rplus_le_reg_r with (r:=h).
              rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r.
              destruct H16, H17.
              apply Rle_trans with(r2:=x+h); auto.
              apply Rplus_le_compat_r; auto.
              unfold In in H8; unfold cc in H8. destruct H8.
              rewrite Rabs_left1. rewrite Rabs_left; auto.
              apply Ropp_le_contravar. apply Rplus_le_reg_r with(r:=x).
              rewrite Rminus_plus_r; rewrite Rplus_comm; tauto.
              apply Rle_minus; tauto. }
            destruct H16, H17, H18.
            apply H15 in H18; auto.
            right; rewrite H18; auto.
    + assert(x ∈ [a,b] /\ (x+h) ∈ [a,b] /\ (x+h)-x>0).
       { split; auto. split; auto.
         rewrite <- R_distr.
         unfold Rminus; rewrite Rplus_opp_r; rewrite Rplus_0_l; auto. }
      apply H in H7.
      destruct H7, H7, H7, H8, H9.
      apply Rplus_le_compat_r with (r:=-f x)in H9.
      apply Rplus_le_compat_r with (r:=-f x)in H10.
      generalize (Req_dec x0 x); intro.
      destruct H11.
      * generalize (Req_dec x1 x); intro.
        destruct H12.
        -- rewrite H11 in H9; rewrite H12 in H10.
           rewrite Rplus_opp_r in H9. rewrite Rplus_opp_r in H10.
           apply Rle_antisym in H9; auto.
           rewrite <- R_distr in H9.
           unfold Rminus in H9; rewrite Rplus_opp_r in H9;
           rewrite Rplus_0_l in H9.
           unfold Rdiv in H9; apply Rmult_eq_compat_r with(r:=h) in H9.
           rewrite Rmult_plus_distr_r in H9; rewrite Rmult_0_l in H9.
           rewrite Rmult_assoc in H9; rewrite Rinv_l in H9; auto.
           rewrite Rmult_1_r in H9.
           unfold Rminus; rewrite Ropp_mult_distr_l; rewrite H9.
           rewrite Rabs_R0.
           apply Rmult_le_pos. apply Rabs_pos.
           unfold pos_inc in H0; destruct H0.
           apply Rlt_le; apply H0.
           unfold In; unfold oc.
           unfold In in H3, H4; unfold cc in H3, H4.
           destruct H3, H4.
           split. apply Rlt_Rminus; auto.
           split. apply Rabs_pos_lt; auto.
           rewrite Rabs_right; auto.
           apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
           rewrite Rplus_comm; apply Rle_trans with(r2:=x+h).
           apply Rplus_le_compat_r with(r:=h); tauto. tauto.
           apply Rgt_ge; auto.
        -- rewrite H11 in H9; rewrite Rplus_opp_r in H9.
           assert (x ∈ [a,b] /\ (x+(x1-x)) ∈ [a,b] /\ x1-x<>0).
            { split; auto.
              split.
              unfold In; unfold cc.
              unfold In in H3, H4, H8; unfold cc in H3, H4, H8.
              destruct H3, H4, H8. split; auto.
              rewrite Rplus_minus. split.
              apply Rle_trans with(r2:=x); tauto.
              apply Rle_trans with (r2:=x+h); tauto.
              apply Rminus_eq_contra; auto. }
           apply H2 in H13. generalize H9; intro.
           apply Rle_trans with(r3:= f x1 + - f x) in H9; auto.
        rewrite <- Rabs_right in H10.
        rewrite <- Rabs_right with(r:=(F(x+h)-F x)/((x+h)-x)+-f x) in H10.
        rewrite <- R_distr in H10.
        unfold Rminus in H10; rewrite Rplus_opp_r in H10;
        rewrite Rplus_0_l in H10.
        rewrite Rplus_minus in H13.
        apply Rle_trans with (r3:=d (Rabs (x1 - x))) in H10; auto.
        apply Rmult_le_reg_r with (r:=Rabs (/h)).
        apply Rabs_pos_lt; apply Rinv_neq_0_compat; auto.
        rewrite Rmult_comm with(r1:=Rabs h); rewrite Rmult_assoc.
        repeat rewrite <- Rabs_mult; rewrite Rinv_r; auto. 
        rewrite Rabs_R1; rewrite Rmult_1_r.
        unfold Rminus. rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
        rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
        apply Rle_trans with(r2:=d (Rabs (x1 - x))); auto.
        unfold pos_inc in H0; destruct H0.
        assert((Rabs(x1-x)) ∈ (0,b-a]/\(Rabs h) ∈ (0,b-a]/\Rabs(x1-x)<=Rabs h).
         { split; unfold In; unfold oc.
           unfold In in H3, H4, H8; unfold cc in H3, H4, H8.
           destruct H3, H4, H8.
           split. apply Rlt_Rminus; auto.
           split. apply Rabs_pos_lt; apply Rminus_eq_contra; auto.
           rewrite Rabs_right.
           unfold Rminus; apply Rplus_le_compat.
           apply Rle_trans with(r2:=x+h); tauto.
           apply Ropp_le_contravar; tauto.
           apply Rge_minus; apply Rle_ge; tauto.
           unfold In in H3, H4; unfold cc in H3, H4.
           destruct H3, H4.
           split.
           split. apply Rlt_Rminus; auto.
           split. apply Rabs_pos_lt; auto.
           rewrite Rabs_right; auto.
           apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
           rewrite Rplus_comm.
           apply Rle_trans with(r2:=x+h).
           apply Rplus_le_compat_r; tauto. tauto.
           apply Rgt_ge; auto.
           unfold In in H8; unfold cc in H8; destruct H8.
           rewrite Rabs_right. rewrite Rabs_right.
           apply Rplus_le_reg_r with(r:=x).
           rewrite Rminus_plus_r; rewrite Rplus_comm; tauto.
           apply Rgt_ge; auto.
           apply Rge_minus; apply Rle_ge; tauto. }
         destruct H16, H17, H18.
         apply H15 in H18; auto.
         right; rewrite H18; auto.
         apply Rle_ge; auto.
         apply Rle_ge; auto.
     * generalize (Req_dec x1 x); intro.
       destruct H12.
       -- rewrite H12 in H10; rewrite Rplus_opp_r in H10.
          assert (x ∈ [a,b] /\ (x+(x0-x)) ∈ [a,b] /\ x0-x<>0).
           { split; auto.
             split.
             unfold In; unfold cc.
             unfold In in H3, H4, H7; unfold cc in H3, H4, H7.
             destruct H3, H4, H8. split; auto.
             rewrite Rplus_minus. split.
             apply Rle_trans with(r2:=x); tauto.
             apply Rle_trans with (r2:=x+h); tauto.
             apply Rminus_eq_contra; auto. }
           apply H2 in H13. generalize H9; intro.
           apply Rle_trans with(r3:= 0) in H9; auto.
           rewrite <- Ropp_involutive with(r:=f x0 + - f x) in H14.
           rewrite <- Rabs_right with(r:=-(f x0 + - f x)) in H14.
           rewrite<-Ropp_involutive with(r:=(F(x+h)-F x)/((x+h)-x)+-f x) in H14.
           rewrite <- Rabs_right with(r:=-((F(x+h)-F x)/((x+h)-x)+-f x)) in H14.
           apply Ropp_le_cancel in H14.
           repeat rewrite Rabs_Ropp in H14.
           rewrite <- R_distr in H14.
           unfold Rminus in H14; rewrite Rplus_opp_r in H14;
           rewrite Rplus_0_l in H14.
           rewrite Rplus_minus in H13.
           apply Rle_trans with (r3:=d (Rabs (x0 - x))) in H14; auto.
           apply Rmult_le_reg_r with (r:=Rabs (/h)).
           apply Rabs_pos_lt; apply Rinv_neq_0_compat; auto.
           rewrite Rmult_comm with(r1:=Rabs h); rewrite Rmult_assoc.
           repeat rewrite <- Rabs_mult; rewrite Rinv_r; auto. 
           rewrite Rabs_R1; rewrite Rmult_1_r.
           unfold Rminus. rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
           rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
           apply Rle_trans with(r2:=d (Rabs (x0 - x))); auto.
           unfold pos_inc in H0; destruct H0.
           assert((Rabs (x0 - x)) ∈ (0,b-a]/\(Rabs h) ∈ (0,b-a]/\
                  Rabs (x0 - x)<=Rabs h).
            { split; unfold In; unfold oc.
              unfold In in H3, H4, H7; unfold cc in H3, H4, H7.
              destruct H3, H4, H7.
           split. apply Rlt_Rminus; auto.
           split. apply Rabs_pos_lt; apply Rminus_eq_contra; auto.
           rewrite Rabs_right.
           unfold Rminus; apply Rplus_le_compat.
           apply Rle_trans with(r2:=x+h); tauto.
           apply Ropp_le_contravar; tauto.
           apply Rge_minus; apply Rle_ge; tauto.
           unfold In in H3, H4; unfold cc in H3, H4.
           destruct H3, H4.
           split.
           split. apply Rlt_Rminus; auto.
           split. apply Rabs_pos_lt; auto.
           rewrite Rabs_right; auto.
           apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
           rewrite Rplus_comm.
           apply Rle_trans with(r2:=x+h).
           apply Rplus_le_compat_r; tauto. tauto.
           apply Rgt_ge; auto.
           unfold In in H7; unfold cc in H7; destruct H7.
           rewrite Rabs_right. rewrite Rabs_right.
           apply Rplus_le_reg_r with(r:=x).
           rewrite Rminus_plus_r; rewrite Rplus_comm; tauto.
           apply Rgt_ge; auto.
           apply Rge_minus; apply Rle_ge; tauto. }
         destruct H16, H17, H18.
         apply H15 in H18; auto.
         right; rewrite H18; auto.
         rewrite <- Ropp_0; apply Ropp_le_ge_contravar; auto.
         rewrite <- Ropp_0; apply Ropp_le_ge_contravar; auto.
      -- assert (x ∈ [a,b] /\ (x+(x1-x)) ∈ [a,b] /\ x1-x<>0).
         { split; auto.
           split.
           unfold In; unfold cc.
           unfold In in H3, H4, H8; unfold cc in H3, H4, H8.
           destruct H3, H4, H8. split; auto.
           rewrite Rplus_minus. split.
           apply Rle_trans with(r2:=x); tauto.
           apply Rle_trans with (r2:=x+h); tauto.
           apply Rminus_eq_contra; auto. }
         assert (x ∈ [a,b] /\ (x+(x0-x)) ∈ [a,b] /\ x0-x<>0).
         { split; auto.
           split.
           unfold In; unfold cc.
           unfold In in H3, H4, H7; unfold cc in H3, H4, H7.
           destruct H3, H4, H8. split; auto.
           rewrite Rplus_minus. split.
           apply Rle_trans with(r2:=x); tauto.
           apply Rle_trans with (r2:=x+h); tauto.
           apply Rminus_eq_contra; auto. }
         apply H2 in H13; apply H2 in H14.
         apply lemma4_3_1 with(r:=f x0 + - f x) in H10; auto.
         destruct H10.
         ++ rewrite <- R_distr in H10.
            unfold Rminus in H10; rewrite Rplus_opp_r in H10;
            rewrite Rplus_0_l in H10.
            rewrite Rplus_minus in H14.
            apply Rle_trans with (r3:=d (Rabs (x0 - x))) in H10; auto.
            apply Rmult_le_reg_r with (r:=Rabs (/h)).
            apply Rabs_pos_lt; apply Rinv_neq_0_compat; auto.
            rewrite Rmult_comm with(r1:=Rabs h); rewrite Rmult_assoc.
            repeat rewrite <- Rabs_mult; rewrite Rinv_r; auto. 
            rewrite Rabs_R1; rewrite Rmult_1_r.
            unfold Rminus. rewrite Rmult_plus_distr_r;
            rewrite Ropp_mult_distr_l.
            rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
            apply Rle_trans with(r2:=d (Rabs (x0 - x))); auto.
            unfold pos_inc in H0; destruct H0.
            assert((Rabs (x0 - x)) ∈ (0,b-a]/\(Rabs h) ∈ (0,b-a]/\
              Rabs (x0 - x)<=Rabs h).
             { split; unfold In; unfold oc.
               unfold In in H3, H4, H7; unfold cc in H3, H4, H7.
               destruct H3, H4, H7.
               split. apply Rlt_Rminus; auto.
               split. apply Rabs_pos_lt; apply Rminus_eq_contra; auto.
               rewrite Rabs_right.
               unfold Rminus; apply Rplus_le_compat.
               apply Rle_trans with(r2:=x+h); tauto.
               apply Ropp_le_contravar; tauto.
               apply Rge_minus; apply Rle_ge; tauto.
               unfold In in H3, H4; unfold cc in H3, H4.
               destruct H3, H4.
               split.
               split. apply Rlt_Rminus; auto.
               split. apply Rabs_pos_lt; auto.
               rewrite Rabs_right; auto.
               apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
               rewrite Rplus_comm.
               apply Rle_trans with(r2:=x+h).
               apply Rplus_le_compat_r; tauto. tauto.
               apply Rgt_ge; auto.
               unfold In in H7; unfold cc in H7; destruct H7.
               rewrite Rabs_right. rewrite Rabs_right.
               apply Rplus_le_reg_r with(r:=x).
               rewrite Rminus_plus_r; rewrite Rplus_comm; tauto.
               apply Rgt_ge; auto.
               apply Rge_minus; apply Rle_ge; tauto. }
            destruct H16, H17, H18.
            apply H15 in H18; auto.
            right; rewrite H18; auto.
         ++ rewrite <- R_distr in H10.
            unfold Rminus in H10; rewrite Rplus_opp_r in H10;
            rewrite Rplus_0_l in H10.
            rewrite Rplus_minus in H13.
            apply Rle_trans with (r3:=d (Rabs (x1 - x))) in H10; auto.
            apply Rmult_le_reg_r with (r:=Rabs (/h)).
            apply Rabs_pos_lt; apply Rinv_neq_0_compat; auto.
            rewrite Rmult_comm with(r1:=Rabs h); rewrite Rmult_assoc.
            repeat rewrite <- Rabs_mult; rewrite Rinv_r; auto. 
            rewrite Rabs_R1; rewrite Rmult_1_r.
            unfold Rminus.
            rewrite Rmult_plus_distr_r; rewrite Ropp_mult_distr_l.
            rewrite Rmult_assoc; rewrite Rinv_r; auto; rewrite Rmult_1_r.
            apply Rle_trans with(r2:=d (Rabs (x1 - x))); auto.
            unfold pos_inc in H0; destruct H0.
            assert((Rabs(x1-x))∈(0,b-a]/\(Rabs h)∈(0,b-a]/\Rabs(x1-x)<=Rabs h).
             { split; unfold In; unfold oc.
               unfold In in H3, H4, H8; unfold cc in H3, H4, H8.
               destruct H3, H4, H8.
               split. apply Rlt_Rminus; auto.
               split. apply Rabs_pos_lt; apply Rminus_eq_contra; auto.
               rewrite Rabs_right.
               unfold Rminus; apply Rplus_le_compat.
               apply Rle_trans with(r2:=x+h); tauto.
               apply Ropp_le_contravar; tauto.
               apply Rge_minus; apply Rle_ge; tauto.
               unfold In in H3, H4; unfold cc in H3, H4.
               destruct H3, H4.
               split.
               split. apply Rlt_Rminus; auto.
               split. apply Rabs_pos_lt; auto.
               rewrite Rabs_right; auto.
               apply Rplus_le_reg_r with (r:=a); rewrite Rminus_plus_r.
               rewrite Rplus_comm.
               apply Rle_trans with(r2:=x+h).
               apply Rplus_le_compat_r; tauto. tauto.
               apply Rgt_ge; auto.
               unfold In in H8; unfold cc in H8; destruct H8.
               rewrite Rabs_right. rewrite Rabs_right.
               apply Rplus_le_reg_r with(r:=x).
               rewrite Rminus_plus_r; rewrite Rplus_comm; tauto.
               apply Rgt_ge; auto.
               apply Rge_minus; apply Rle_ge; tauto. }
            destruct H16, H17, H18.
            apply H15 in H18; auto.
            right; rewrite H18; auto.
Qed.
