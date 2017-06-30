theory T2_Demo_Arbol
imports Main
begin

section {* Definición del tipo de datos de árboles *}

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

section {* Demostración de propiedades de árboles *}  
  
text {* Prop.: Las hojas son distintas de los nodos. *}  
lemma "Hoja \<noteq> Nodo l x r"
by simp

text {* (espejo t) es la imagen especular del árbol t. Por ejemplo, 
     espejo (Nodo Hoja (9::int) (Nodo Hoja 4 Hoja))
             = Nodo (Nodo Hoja 4 Hoja) 9 Hoja
     espejo (Nodo (Nodo Hoja a Hoja) b t)
            = Nodo (espejo t) b (Nodo Hoja a Hoja)
*}
fun espejo :: "'a arbol \<Rightarrow> 'a arbol" 
where
  "espejo Hoja         = Hoja" 
| "espejo (Nodo i x d) = Nodo (espejo d) x (espejo i)"

value "espejo (Nodo Hoja (9::int) (Nodo Hoja 4 Hoja))"
lemma "espejo (Nodo Hoja (9::int) (Nodo Hoja 4 Hoja))
       = Nodo (Nodo Hoja 4 Hoja) 9 Hoja" by simp
value "espejo (Nodo (Nodo Hoja a Hoja) b t)"
lemma "espejo (Nodo (Nodo Hoja a Hoja) b t)
       = Nodo (espejo t) b (Nodo Hoja a Hoja)" by simp

text {* Prop.: La función espejo es idempotente. *}       
lemma espejo_espejo [simp]: 
  "espejo (espejo t) = t"
apply (induction t)
apply auto
done

section {* Ejemplo de función recursiva no primitiva recursiva *}

text {* (intercala x ys) es la lista obtenida intercalando x entre los
  elementos de ys. Por ejemplo, 
     intercala a [x,y,z] = [x, a, y, a, z]" by simp
*} 
fun intercala :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" 
where
  "intercala a []       = []" 
| "intercala a [x]      = [x]" 
| "intercala a (x#y#zs) = x # a # intercala a (y#zs)"

value "intercala a [x,y,z]"
lemma "intercala a [x,y,z] = [x, a, y, a, z]" by simp

end
