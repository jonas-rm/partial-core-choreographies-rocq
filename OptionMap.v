Section OptionMap.

Parameter T U : Type.

Parameter T_dec : forall (t1 t2:T), {t1 = t2} + {t1<>t2}.

Inductive OptionMap : Type :=
  | Nil : OptionMap
  | Add : T -> U -> OptionMap -> OptionMap.

Fixpoint get (m:OptionMap) (t:T) (default:U) : U :=
  match m with
  | Nil => default
  | Add t' u m' => match (T_dec t t') with
                   | left _ => u
                   | right _ => get m' t default
  end end.

Fixpoint is_defined (m:OptionMap) (t:T) : Prop :=
  match m with
  | Nil => False
  | Add t' u m' => match (T_dec t t') with
                   | left _ => True
                   | right _ => is_defined m' t
  end end.

Lemma Add_get_eq : forall m t u default, get (Add t u m) t default = u.
intros; simpl; elim T_dec; intros; auto; elim b; auto.
Qed.

Lemma Add_get_diff: forall m t u t' default, t <> t' -> get (Add t u m) t' default = get m t' default.
intros; simpl; elim T_dec; intros; auto; elim H; auto.
Qed.

Lemma undefined : forall m t default, ~(is_defined m t) -> get m t default = default.
induction m; intros; simpl; auto.
simpl in H.
revert H; elim T_dec; simpl; auto.
intros; elim H; auto.
Qed.

End OptionMap.
