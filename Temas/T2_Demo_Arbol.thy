theory T2_Demo_Arbol
imports Main
begin

text {* ('a arbol) es el tipo de dato de los śrboles con valores en en
los nodos. *} 
datatype 'a arbol = Hoja | Nodo "'a arbol" 'a "'a arbol"

text {* El árbol
      9
     / \
   .    4
        /\
       .   .
  se define como sigue       
*}
abbreviation ejArbol1 :: "int arbol" 
where
  "ejArbol1 \<equiv> Nodo Hoja (9::int) (Nodo Hoja 4 Hoja)"

text {* Prop.: Las hojas son distintas de los nodos. *}  
lemma "Hoja \<noteq> Nodo l x r"
by simp

fun mirror :: "'a arbol \<Rightarrow> 'a arbol" where
"mirror Hoja = Hoja" |
"mirror (Nodo l x r) = Nodo (mirror r) x (mirror l)"

value "mirror(Nodo (Nodo Hoja a Hoja) b t)"

lemma mirror_mirror[simp]: "mirror(mirror t) = t"
apply(induction t)
apply auto
done

text{* An example of fun: beyond one equation per constructor *}

fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sep a [] = []" |
"sep a [x] = [x]" |
"sep a (x#y#zs) = x # a # sep a (y#zs)"

value "sep a [x,y,z]"

end
