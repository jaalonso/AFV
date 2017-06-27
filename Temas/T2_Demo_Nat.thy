theory T2_Demo_Nat
imports Main
begin

text {* (suma m n) es la suma de los números naturales m y n. Por
  ejemplo,
     suma (Suc (Suc 0)) (Suc (Suc (Suc 0)))
     = Suc (Suc (Suc (Suc (Suc 0))))
*} 
fun suma :: "nat \<Rightarrow> nat \<Rightarrow> nat" 
where
  "suma 0 n       = n" 
| "suma (Suc m) n = Suc (suma m n)"

value "suma (Suc (Suc 0)) (Suc (Suc (Suc 0)))"
lemma "suma (Suc (Suc 0)) (Suc (Suc (Suc 0)))
       = Suc (Suc (Suc (Suc (Suc 0))))" by simp

text {* Prop: m + 0 = m *}

text {* Demostración aplicativa *}

lemma suma_0: "suma m 0 = m"
apply (induction m)
apply auto
done

text {* Demostración estructurada *}

lemma suma_0': "suma m 0 = m"
by (induction m) auto

end
