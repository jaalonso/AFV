theory Opcionales
imports Main
begin

text {* (busca ps x) es el segundo elemento del primer par de ps cuyo
  primer elemento es x y None si ningún elemento de ps tiene un primer
  elemento igual a x. Por ejemplo,
     busca [(1::int,2::int),(3,6)] 3 = Some 6
     busca [(1::int,2::int),(3,6)] 2 = None
*}
fun busca :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option"
where
  "busca [] x           = None" 
| "busca ((a,b) # ps) x = (if a = x 
                            then Some b 
                            else busca ps x)"

value "busca [(1::int,2::int),(3,6)] 3"
lemma "busca [(1::int,2::int),(3,6)] 3 = Some 6" by simp
value "busca [(1::int,2::int),(3,6)] 2"
lemma "busca [(1::int,2::int),(3,6)] 2 = None" by simp

end
