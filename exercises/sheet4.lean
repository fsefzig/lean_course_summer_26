import Lecture-notes.Lecture5.Examples5

open MyQuotient

lemma q_eq_rest {n m1 m2 : ℤ} (hn : n ≠ 0) : (q n m1) = q n m2 ↔ (m1 % n = m2 % n) := by
  sorry

lemma f_injective_of_left_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) :
    Function.Injective f := by
  sorry

lemma f_surjective_of_right_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ y, f (g y) = y) :
    Function.Surjective f := by
  sorry

lemma f_surjective_of_range_eq {α β : Type} (f : α → β) (g : β → α) (Set.range f = Set.univ) :
    Function.Surjective f := by
  sorry


lemma mul_dvd_of_dvd_of_gcd_eq_one {a b c : ℤ} (h1 : a ∣ c) (h2 : b ∣ c) (h3 : Int.gcd a b = 1) : a * b ∣ c := by
  sorry
