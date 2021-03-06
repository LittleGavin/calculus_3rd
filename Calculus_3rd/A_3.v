Require Export Basic.
Require Export lemma.


(* 函数f在闭区间[a,b]上一致连续 *)
Definition uniform_continuous f (a b:R) :=  
  exists f1, pos_inc f1 (0,b-a] /\
  bounded_rec_f f1 (0,b-a] /\
  (forall x h:R, x ∈ [a,b] /\ (x+h) ∈ [a,b] /\ h<>0 ->
  (Rabs (f(x+h) - f(x))) <= f1(Rabs h)).

(* 函数f在闭区间[a,b]上一致可导 *)
Definition uniform_derivability F (a b:R) := 
  exists d, pos_inc d (0,b-a] /\
  bounded_rec_f d (0,b-a] /\
  exists f M, 0<M /\ forall x h:R, x ∈ [a,b] /\ (x+h) ∈ [a,b] /\ h<>0 ->
  Rabs (F(x+h) - F(x) - f(x)*h) <= M*(Rabs h)*d(Rabs h).

(* 函数f在闭区间[a,b]上强可导 *)
Definition str_derivability F (a b:R) :=
  exists f M, 0<M /\ forall x h:R, x ∈ [a,b] /\ (x+h) ∈ [a,b] ->
  Rabs (F(x+h) - F(x) - f(x)*h) <= M*(h^2).

(* 函数F在闭区间[a,b]上的导数为函数f *)
Definition derivative F f a b := 
  exists d, pos_inc d (0,b-a] /\
  bounded_rec_f d (0,b-a] /\
  exists M:R, 0<M /\ forall x h:R, x ∈ [a,b] /\ (x+h) ∈ [a,b] /\ h<>0 ->
  Rabs (F(x+h) - F(x) - f(x)*h) <= M*(Rabs h)*d(Rabs h).


(* 函数F在闭区间[a,b]上的强可导导数为函数f *)
Definition str_derivative F f (a b:R) := 
  exists M:R, 0<M /\ forall x h:R, x ∈ [a,b] /\ (x+h) ∈ [a,b] ->
  Rabs (F(x+h) - F(x) - f(x)*h) <= M*(h^2).

(* 设 F(x),G(x)一致(强)可导，并且导数分别是f(x),g(x) *)

(* 对任意常数c，cF(x)一致(强)可导，且其导数分别是cf(x) *)
Theorem Theorem3_1_1 : forall (a b c:R) F f,
  derivative F f a b -> derivative (mult_real_f c F) (mult_real_f c f) a b.
Proof.
  intros a b c F f .
  unfold derivative; intro.
  destruct H, H, H0, H1, H1.
  exists x; split; auto. split; auto.
  generalize (total_eq_or_neq c 0); intro. destruct H3.
  - exists x0. split; auto; intros.
    apply H2 in H4. unfold mult_real_f; rewrite H3.
    repeat rewrite Rmult_0_l. unfold Rminus; rewrite Ropp_0;
    repeat rewrite Rplus_0_l; rewrite Rabs_R0.
    apply Rle_trans with (r2:=Rabs(F(x1+h)-F x1-f x1*h)); auto. 
    apply Rabs_pos.
  - exists (Rabs c * x0). split.
    apply Rmult_lt_0_compat; auto.
    apply Rabs_pos_lt; auto. intros. apply H2 in H4. 
    unfold mult_real_f. rewrite Rmult_assoc.
    rewrite <- Rmult_minus_distr_1_3 with
    (r:=c)(r1:=(F(x1+h)))(r2:=F x1)(r3:=f x1*h).
    rewrite Rabs_mult; repeat rewrite Rmult_assoc; apply Rmult_le_compat_l.
    apply Rabs_pos. repeat rewrite <- Rmult_assoc; apply H4. 
Qed.


Theorem Theorem3_1_1' : forall (a b c:R) F f,
  str_derivative F f a b -> str_derivative (mult_real_f c F) (mult_real_f c f) a b.
Proof.
  intros.
  unfold str_derivative in H; unfold str_derivative.
  destruct H, H.
  generalize (total_eq_or_neq c 0); intro.
  destruct H1.
  - exists x. split; auto; intros.
    apply H0 in H2.
    unfold mult_real_f; rewrite H1. repeat rewrite Rmult_0_l.
    unfold Rminus; rewrite Ropp_0; repeat rewrite Rplus_0_l; rewrite Rabs_R0.
    apply Rmult_le_pos. apply Rlt_le; auto.
    apply pow2_ge_0.
  - exists (Rabs c * x).
    split.
    apply Rmult_lt_0_compat; auto. apply Rabs_pos_lt; auto.
    intros. apply H0 in H2.
    unfold mult_real_f. rewrite Rmult_assoc.
    rewrite <- Rmult_minus_distr_1_3 with
    (r:=c)(r1:=(F(x0+h)))(r2:=F x0)(r3:=f x0*h).
    rewrite Rabs_mult; repeat rewrite Rmult_assoc;
    apply Rmult_le_compat_l; auto.
    apply Rabs_pos.
Qed.


Lemma total_le_gt : forall r1 r2, {r1 <= r2} + {r1 > r2}.
Proof.
  intros. generalize(total_order_T r1 r2); intro.
  destruct H. left. destruct s. left; auto. right; auto.
  right; auto.
Qed.

Definition max_f1_f2 (f1 f2 : R -> R) := fun x:R =>
  match (total_le_gt (f1 x)(f2 x)) with
  | left _ => f2 x
  | right _ => f1 x
  end.

Lemma existence_f : forall a b f1 f2, 
  pos_inc f1 (0,b-a] /\
  (forall r1:R, exists z1:R, z1 ∈ (0,b-a] /\ r1 < Rabs(1/(f1 z1))) /\
  pos_inc f2 (0,b-a] /\
  (forall r2:R, exists z2:R, z2 ∈ (0,b-a] /\ r2 < Rabs(1/(f2 z2))) ->
  exists f3, (pos_inc f3 (0,b-a] /\
  (forall r3:R, exists z3:R, z3 ∈ (0,b-a] /\ r3 < Rabs(1/(f3 z3))) /\
  (forall a:R, f1 a <= f3 a /\ f2 a <= f3 a)).
Proof.
  intros. exists (max_f1_f2 f1 f2).
  destruct H, H0, H1. split.
  - unfold pos_inc. unfold pos_inc in H, H1.
    split; intros.
    + destruct H, H1. generalize H3; intros. apply H in H3; apply H1 in H6.
      unfold max_f1_f2; destruct total_le_gt; auto.
    + destruct H, H1; generalize H5; intros.
      apply H6 in H5; auto. apply H7 in H8; auto.
      unfold max_f1_f2.  destruct total_le_gt.
      * destruct total_le_gt; auto.
        apply Rle_trans with(r2:=f2 z2); auto.
        apply Rlt_le; auto.
      * destruct total_le_gt; auto.
        eapply Rle_trans. apply H5 . apply r0.
  - split; intros.
    generalize(H0 r3); intro.
    generalize(H2 r3); intro. clear H0; clear H2.
    destruct H3, H0. destruct H4, H3.
    generalize(classic (exists z3:R, z3∈(0,b-a]/\
    r3 < Rabs(1/(if total_le_gt(f1 z3)(f2 z3) then f2 z3 else f1 z3)))); intro.
    destruct H5; auto. generalize H5; intro.
    apply not_exist with(x:=x0) in H5; auto. apply Rnot_lt_le in H5.
    apply not_exist with(x:=x) in H6; auto. apply Rnot_lt_le in H6.
    unfold max_f1_f2. destruct total_le_gt.
    + apply Rlt_not_le in H4; contradiction.
    + exists x. destruct total_le_gt.
      * unfold pos_inc in H, H1.
        destruct H, H1.
        generalize(H x H0); intro; apply Rinv_0_lt_compat in H9.
        generalize(H x0 H3); intro; apply Rinv_0_lt_compat in H10.
        generalize(H1 x H0); intro; apply Rinv_0_lt_compat in H11.
        generalize(H1 x0 H3); intro; apply Rinv_0_lt_compat in H12.
        assert(r3 > 0) as R3_ge_0. 
         { apply Rlt_not_eq in H10. unfold Rdiv in H5.
           rewrite Rmult_1_l in H5. apply not_eq_sym in H10.
           apply Rabs_pos_lt in H10. 
           apply Rlt_le_trans with(r3:=r3)in H10; auto. }
        unfold Rdiv in H2; rewrite Rmult_1_l in H2; rewrite Rabs_right in H2;
        try apply Rgt_ge; try apply Rlt_inv in H2; auto.
        unfold Rdiv in H4; rewrite Rmult_1_l in H4; rewrite Rabs_right in H4;
        try apply Rgt_ge; try apply Rlt_inv in H4; auto.
        unfold Rdiv in H5; rewrite Rmult_1_l in H5; rewrite Rabs_right in H5;
        try apply Rgt_ge; try apply Rinv_le in H5; auto.
        unfold Rdiv in H6; rewrite Rmult_1_l in H6; rewrite Rabs_right in H6;
        try apply Rgt_ge; try apply Rinv_le in H6; auto.
        clear H9 H10 H11 H12.
        generalize (Rtotal_order x x0); intro.
        destruct H9.
        { generalize H9; intro.
          apply H7 in H9; apply H8 in H10; auto.
          apply Rge_le in H6.
          generalize(Rlt_le_trans (f2 x0)(/r3)(f2 x) H4 H6); intro.
          apply Rlt_not_le in H11; contradiction. }
        destruct H9.
        { rewrite H9 in H6. apply Rlt_not_ge in H4. contradiction. }
        { apply Rgt_lt in H9.
          generalize H9; intro.
          apply H7 in H9; apply H8 in H10; auto.
          apply Rge_le in H5.
          generalize(Rlt_le_trans (f1 x)(/r3)(f1 x0) H2 H5); intro.
          apply Rlt_not_le in H11; contradiction. }
      * split; auto.
    + unfold max_f1_f2. destruct total_le_gt.
      * split; auto. apply Rge_refl.
      * split. apply Rle_refl.
        apply Rge_le; apply Rgt_ge; auto.
Qed.


(* f1(x) f2(x)均正值单增，则f1(x)+f2(x)正值单增 *)
Lemma th3' : forall f1 f2 (q:R_Ensemble),
  pos_inc f1 q -> pos_inc f2 q -> pos_inc (plus_Fu f1 f2) q.
Proof.
  intros f1 f2 q.
  unfold pos_inc; intros.
  destruct H, H0.
  split; intros.
  - generalize H3 as H4; intro; apply H in H3; apply H0 in H4.
    unfold plus_Fu.
    rewrite <- Rplus_0_r.
    apply Rplus_gt_compat; auto.
  - generalize (H1 z1 z2 H3 H4 H5); intros.
    generalize (H2 z1 z2 H3 H4 H5); intros.
    unfold plus_Fu.
    apply Rplus_le_compat; auto.
Qed.

(* F(x)+G(x)一致(强)可导,且其导数分别是f(x)和g(x) *)
Theorem Theorem3_1_2 : forall F G f g (a b:R),
  derivative F f a b -> derivative G g a b ->
  derivative (plus_Fu F G) (plus_Fu f g) a b.
Proof.
  intros F G f g a b.
  unfold derivative; unfold bounded_rec_f; intros.
  destruct H, H, H1, H2, H2. rename x into d1; rename x0 into M1.
  destruct H0, H0, H4, H5, H5. rename x into d2; rename x0 into M2.
  assert (exists d3, pos_inc d3 (0,b-a] /\ (forall r3:R,
          exists z3:R, z3 ∈ (0,b-a] /\ r3 < Rabs(1/(d3 z3))) /\
          forall a:R, d1 a <= d3 a /\ d2 a <= d3 a).
   { apply existence_f with (a:=a)(b:=b) (f1:=d1) (f2:=d2). 
     split; auto. }
  destruct H7, H7, H8. rename x into d3.
  exists d3; split; auto. split; auto.
  exists (M1 + M2); intros.
  split.
  apply Rplus_lt_0_compat; auto. intros.
    generalize H10; intro.
    apply H3 in H10; apply H6 in H11.
    unfold plus_Fu.
    rewrite Rmult_plus_distr_r with (r1:=(f x))(r2:=(g x))(r3:=h).
    rewrite plus_ab_minus_cd with (a:=F(x+h))(b:=G(x+h))(c:=F x)
                                  (d:=G x)(e:=f x*h)(f:=g x*h).
    assert (Rabs(F(x+h) - F x - f x*h)+Rabs(G(x+h) - G x - g x*h)
            <= M1*(Rabs h)*d1(Rabs h) + M2*(Rabs h)*d2(Rabs h)).
     { apply Rplus_le_compat; auto. }
    apply Rle_abcd with (a:=Rabs(F(x+h)-F x-f x*h+(G(x+h)-G x-g x*h)))
                        (b:=Rabs(F(x+h)-F x-f x*h)+Rabs(G(x+h)-G x-g x*h))
                        (c:=M1*(Rabs h)*d1(Rabs h)+M2*(Rabs h)*d2(Rabs h))
                        (d:=(M1+M2)*(Rabs h)*d3(Rabs h)).
    + apply Rabs_triang.
    + rewrite Rmult_plus_distr_r.
      rewrite Rmult_plus_distr_r.
      apply Rplus_le_compat; apply Rmult_le_compat_l.
      apply Rmult_le_pos. apply Rlt_le; auto. apply Rabs_pos. apply H9.
      apply Rmult_le_pos. apply Rlt_le; auto. apply Rabs_pos. apply H9.
    + auto.
Qed.

Theorem Theorem3_1_2' : forall F G f g (a b:R),
  str_derivative F f a b -> str_derivative G g a b ->
  str_derivative (plus_Fu F G) (plus_Fu f g) a b.
Proof.
  intros F G f g a b.
  unfold str_derivative; intros.
  destruct H, H, H0, H0.
  exists (x + x0); intros.
  split.
  apply Rplus_lt_0_compat; auto. intros.
    generalize H3; intro.
    apply H2 in H3; apply H1 in H4.
    unfold plus_Fu.
    rewrite Rmult_plus_distr_r with (r1:=(f x1))(r2:=(g x1))(r3:=h).
    rewrite plus_ab_minus_cd with (a:=F(x1+h))(b:=G(x1+h))(c:=F x1)
                                  (d:=G x1)(e:=f x1*h)(f:=g x1*h).
    assert (Rabs(F(x1+h) - F x1 - f x1*h)+Rabs(G(x1+h) - G x1 - g x1*h)
            <= (x + x0) * h ^ 2).
     { rewrite Rmult_plus_distr_r. 
       apply Rplus_le_compat; auto. }
    apply Rle_abcd with (a:=Rabs(F(x1+h)-F x1-f x1*h+(G(x1+h)-G x1-g x1*h)))
                        (b:=Rabs(F(x1+h)-F x1-f x1*h)+Rabs(G(x1+h)-G x1-g x1*h))
                        (c:=x*h^2+x0*h^2)
                        (d:=(x+x0)*h^2).
    + apply Rabs_triang.
    + rewrite Rmult_plus_distr_r.
      apply Rle_refl.
    + rewrite <-Rmult_plus_distr_r; auto.
Qed.

Lemma th3 : forall (a b c:R) f, c > 0 -> pos_inc f (0, b-a] ->
  pos_inc (Com_F_c f c) (0, (b/c-a/c)].
Proof.
  intros a b c f C.
  unfold pos_inc; unfold Com_F_c; intro.
  assert ( forall z, z ∈ (0,(b / c - a / c)] ->(c * z) ∈ (0,b-a] ).
   { unfold In; unfold oc; intros.
     rewrite <- Rinv_minus_distr_r in H0.
     unfold Rdiv in H0; destruct H0; split.
     apply Rmult_0_lt_reg in H0; auto.
     apply Rinv_0_lt_compat; auto.
     apply Rlt_x_le with (r:=c); auto. rewrite Rmult_eq_r.
     unfold Rdiv; tauto.
     apply Rgt_not_eq; auto.
     apply Rgt_not_eq; auto. }
  destruct H; split; intros.
  - apply H0 in H2; apply H in H2; auto.
  - apply H0 in H2; apply H0 in H3; apply H1; auto.
    apply Rmult_lt_compat_l; auto.
Qed.


(*F(cx+d)一致（强）可导，且其导数为cf(cx+d)*)
Theorem Theorem3_1_3 : forall F f (a b c d:R),
  c > 0 -> derivative F f a b ->
  derivative (Com_F F c d) (mult_real_f c (Com_F f c d))((a-d)/c)((b-d)/c).
Proof.
intros F f a b c d C.
  unfold derivative; intro.
  destruct H, H, H0, H1, H1. rename x into p; rename x0 into M.
  exists (Com_F_c p c); split.
  apply th3; auto.
  rewrite Rminus_distr; rewrite R_distr; rewrite Rminus_plus_r; auto.
  split.
  unfold bounded_rec_f; unfold bounded_rec_f in H0; intros.
  generalize(H0 M0); intro. destruct H3, H3, H3.
  exists (x/c). split.
  - unfold In; unfold oc. split.
    + rewrite <- Rdiv_minus_distr; rewrite Rminus_distr.
      rewrite R_distr; rewrite Rminus_plus_r.
      unfold Rdiv; apply Rmult_lt_0_compat; auto.
      apply Rinv_0_lt_compat; auto.
    + rewrite <- Rdiv_minus_distr; apply Rlt_x_le_reg; auto;
      rewrite Rminus_distr.
      rewrite R_distr; rewrite Rminus_plus_r; auto.
  - unfold Com_F_c. rewrite Rmult_par_inv_eq. rewrite Rmult_eq_r; auto.
    apply Rgt_not_eq; auto.  apply Rgt_not_eq; auto.
  - unfold Com_F; unfold Com_F_c.
    exists (c*M); intros.
    split. apply Rmult_lt_0_compat; auto.
    intros.
    assert ((c*x+d) ∈ [a,b] /\ ((c*x+d)+(c*h)) ∈ [a,b]).
     { unfold In; unfold cc; unfold In in H3; unfold cc in H3.
       destruct H3, H3, H4.
       assert(a<b). 
       { unfold Rdiv in H3; 
         apply Rmult_lt_reg_r with (r:=/c) in H3; auto.
         unfold Rminus in H3. eapply Rplus_lt_reg_r; apply H3.
         apply Rinv_0_lt_compat; auto. }
       split; split; auto.
       - apply Rplus_le_3_r.
         apply Rinv_le_r with(r:=c); auto.
         rewrite Rmult_eq_r with (r:=c)(r1:=x); auto.
         apply Rgt_not_eq; auto.
       - rewrite Rplus_comm  with (r1:=c*x)(r2:=d).
         rewrite Rplus_assoc; rewrite Rplus_comm. apply Rplus_le_3_r .
         rewrite <- Rmult_plus_distr_l.
         apply Rinv_le_r with (r:=c); auto.
         rewrite Rmult_eq_r. tauto.
         apply Rgt_not_eq; auto. }
    assert((c*x+d) ∈ [a,b] /\ (c*x+d+c*h) ∈ [a,b] /\ c*h<>0).
     { destruct H4. split; auto. split; auto. 
       apply Rmult_integral_contrapositive_currified.
       apply Rgt_not_eq; auto. tauto. }
    clear H4; apply H2 in H5.
    unfold mult_real_f; unfold Com_F.
    rewrite Rmult_plus_distr_l.
    rewrite Rplus_assoc with(r1:=(c*x))(r2:=d)(r3:=(c*h)) in H5.
    rewrite Rplus_comm  with (r1:=d)(r2:=c*h) in H5. 
    rewrite <- Rplus_assoc in H5.
    rewrite <- Rmult_assoc with(r1:=(f(c*x+d)))(r2:=c)(r3:=h) in H5.
    rewrite Rmult_comm with (r1:=c)(r2:=(f (c*x + d))).
    rewrite Rmult_comm with (r1:=c)(r2:=M). 
    rewrite Rabs_mult in H5. rewrite Rabs_right with (r:=c)in H5.
    rewrite Rmult_assoc with(r1:=M)(r2:=c)(r3:=Rabs h); auto.
    unfold Rge; auto.
Qed.


Theorem Theorem3_1_3' : forall F f (a b c d:R),
  c > 0 -> str_derivative F f a b ->
  str_derivative (Com_F F c d) (mult_real_f c (Com_F f c d))((a-d)/c)((b-d)/c).
Proof.
intros F f a b c d C.
  unfold str_derivative; intro.
  destruct H, H. rename x into M.
  exists (c^2*M); intros.
  split. apply Rmult_lt_0_compat; auto.
  assert(c ^ 2 = c*c). { ring. }
  rewrite H1. apply Rmult_lt_0_compat; auto.
  intros.
  generalize(total_eq_or_neq h 0); intro.
  destruct H2.
  - rewrite H2. rewrite Rplus_0_r.
    rewrite Rmult_0_r. repeat rewrite <- Rsqr_pow2.
    rewrite Rsqr_0. rewrite Rmult_0_r.
    rewrite Rminus_0_r. rewrite Rminus_diag_eq; auto.
    rewrite Rabs_R0. apply Rle_refl.
  - assert ((c*x+d) ∈ [a,b] /\ ((c*x+d)+(c*h)) ∈ [a,b]).
     { unfold In; unfold cc; unfold In in H1; unfold cc in H1.
       destruct H1, H1, H3.
       assert(a<b). 
        { unfold Rdiv in H1; 
          apply Rmult_lt_reg_r with (r:=/c) in H1; auto.
          unfold Rminus in H1. eapply Rplus_lt_reg_r; apply H1.
          apply Rinv_0_lt_compat; auto. }
       split; split; auto.
       - apply Rplus_le_3_r.
         apply Rinv_le_r with(r:=c); auto.
         rewrite Rmult_eq_r with (r:=c)(r1:=x); auto.
         apply Rgt_not_eq; auto.
       - rewrite Rplus_comm  with (r1:=c*x)(r2:=d).
         rewrite Rplus_assoc; rewrite Rplus_comm. apply Rplus_le_3_r .
         rewrite <- Rmult_plus_distr_l.
         apply Rinv_le_r with (r:=c); auto.
         rewrite Rmult_eq_r. tauto.
         apply Rgt_not_eq; auto. }
         assert((c*x+d) ∈ [a,b] /\ (c*x+d+c*h) ∈ [a,b] /\ c*h<>0).
          { destruct H3. split; auto. split; auto. 
            apply Rmult_integral_contrapositive_currified.
            apply Rgt_not_eq; auto. tauto. }
    clear H4; apply H0 in H3.
    unfold mult_real_f; unfold Com_F.
    rewrite Rmult_plus_distr_l.
    rewrite Rplus_assoc with(r1:=(c*x))(r2:=d)(r3:=(c*h)) in H3.
    rewrite Rplus_comm  with (r1:=d)(r2:=c*h) in H3. 
    rewrite <- Rplus_assoc in H3.
    rewrite <- Rmult_assoc with(r1:=(f(c*x+d)))(r2:=c)(r3:=h) in H3.
    rewrite Rmult_comm with (r1:=c)(r2:=(f (c*x + d))).
    assert(M*(c*h)^2=c^2*M*h^2). { ring. }
    rewrite <- H4; auto.
Qed.


(*可加性*)
Definition additivity (S:R->R->R)(a b:R):=
  forall(w1 w2 w3:R), w1 ∈ [a,b] /\ w2 ∈ [a,b] /\w3 ∈ [a,b] -> 
  S w1 w2 + S w2 w3 = S w1 w3. 

(*非负性*)
Definition nonnegativity (S:R->R->R)(f:R->R)(a b:R):=
  forall(w1 w2:R), w1 ∈ [a,b] /\ w2 ∈ [a,b] /\ w2 - w1 > 0 ->
  (forall m:R, (forall x:R, x ∈ [w1,w2] -> m <= f x) -> m*(w2-w1) <= S w1 w2) /\
  (forall M:R, (forall x:R, x ∈ [w1,w2] -> M >= f x) -> S w1 w2 <= M*(w2-w1)).

(*积分系统*)
Definition integ_sys (S:R->R->R)(f:R->R)(a b:R) :=
  additivity S a b /\ nonnegativity S f a b.

(*可积*)
Definition integrable (f:R->R)(a b:R) :=
  exists S, integ_sys S f a b /\
  forall S':R->R->R, integ_sys S' f a b -> S = S'.


(* 积分严格不等式 *)
Definition strict_unequal (S:R->R->R)(f:R->R)(a b:R) :=
  integ_sys S f a b ->
  forall w1 w2:R, w1  ∈ [a,b] /\ w2 ∈ [a,b] /\ w2 - w1 > 0 ->
  (forall m:R, (forall x:R, x ∈ [w1,w2] -> m < f x) -> m*(w2 - w1) < S w1 w2) /\
  (forall M:R, (forall x:R, x ∈ [w1,w2] -> M > f x) -> S w1 w2 < M*(w2 - w1)).


Lemma equ_s : forall (S:R->R->R) (f G:R->R) (a b:R),
  integ_sys S f a b ->
  forall y, y ∈ [a,b] -> (forall x :R, x ∈ [a,b] -> G x = S y x) ->
  forall u v:R, u ∈ [a,b] /\ v ∈ [a,b] ->
  S u v = S y v - S y u /\ S y v - S y u  = G v - G u.
Proof.
  intros.
  unfold integ_sys in H; intros.
  destruct H; unfold additivity in H; split.
  - apply Rplus_eq_reg_r with (r:=(S y u)).
    rewrite Rminus_plus_r with (r1:=(S y v)) (r:=(S y u)).
    rewrite Rplus_comm; apply H.
    split; auto.
  - destruct H2; repeat rewrite H1; auto.
Qed.

(* 估值定理 *)
Theorem Valuation_Theorem :forall (S:R->R->R) (f G:R->R)(a b:R),
  integ_sys S f a b ->
  forall y, y ∈ [a,b] -> (forall x:R, x ∈ [a,b] -> G x = S y x) ->
  strict_unequal S f a b ->
  forall u v, u ∈ [a,b] /\ v ∈ [a,b] /\ v - u > 0 ->
  exists x1 x2, x1 ∈ [u,v] /\ x2 ∈ [u,v] /\
  (f x1)*(v-u) <= G(v) - G(u) <= (f x2)*(v-u).
Proof.
  intros.
  unfold strict_unequal in H2.
  generalize H as l; intro.
  apply H2 with (w1:=u)(w2:=v) in H; auto. clear H2.
  destruct H, H3, H4.
  assert (exists x1, x1 ∈ [u,v] /\ (f x1)*(v-u) <= G(v) - G(u)).
   { generalize (classic(exists x1, x1 ∈ [u,v] /\ (f x1)*(v-u) <= G(v) - G(u))).
     intros. destruct H6; auto.
     assert (G v - G u < S u v). 
      { generalize (H ((G v - G u)/(v-u))); intros; clear H.
        unfold Rdiv in H7.
        rewrite Rinv_mult_rgt0 with (r1:=(G v - G u))(r:=(v - u))in H7; auto.
        apply H7; intros.
        apply not_exist with (x:=x) in H6. apply Rnot_le_gt in H6.
        apply Rgt_mult in H6; auto. apply H. }
     rewrite H1 in H7; auto. rewrite H1 in H7; auto.
     assert ( S u v = S y v - S y u /\ S y v - S y u = G v - G u).
      { apply equ_s with (f:=f)(a:=a)(b:=b); auto. }
     destruct H8.
     rewrite H8 in H7; apply Rlt_irrefl in H7; contradiction. }
  assert (exists x2, x2 ∈ [u,v] /\ (f x2)*(v-u) >= G(v) - G(u)).
   { generalize (classic(exists x2, x2 ∈ [u,v] /\ (f x2)*(v-u) >= G(v) - G(u))).
     intros. destruct H7; auto.
     assert (G v - G u > S u v). 
      { generalize (H2 ((G v - G u)/(v-u))); intros; clear H2.
        unfold Rdiv in H8.
        rewrite Rinv_mult_rgt0 with (r1:=(G v - G u))(r:=(v - u))in H8; auto.
        apply H8; intros.
        apply not_exist with (x:=x) in H7. apply Rnot_ge_lt in H7.
        apply Rlt_mult in H7; auto. apply H2. }
     rewrite H1 in H8; auto. rewrite H1 in H8; auto.
     assert ( S u v = S y v - S y u /\ S y v - S y u = G v - G u).
      { apply equ_s with (f:=f)(a:=a)(b:=b); auto. }
     destruct H9.
     rewrite H9 in H8; apply Rlt_irrefl in H8; contradiction. }
  destruct H6, H6, H7, H7.
  exists x, x0.
  split; auto. split; auto. split; auto.
  apply Rge_le; auto.
Qed.