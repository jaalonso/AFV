theory ABB
imports "~~/src/HOL/Library/Tree"
begin

text {* Se declara que la función Let como simplificador. *}
declare Let_def [simp]

section "Funciones sobre los árboles binarios de búsqueda (ABB)"

text {* Ejemplos de árboles de búsqueda. *} 
abbreviation abb1 :: "int tree" 
where
  "abb1 \<equiv> \<langle>\<langle>\<rangle>, 3::int, \<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>\<rangle>"

text {* (pertenece t ) se verifica si x es un elemento del árbol t.  Por
  ejemplo,
     pertenece abb1 3 = True
     pertenece abb1 5 = False
*}  
fun pertenece :: "('a::linorder) tree \<Rightarrow> 'a \<Rightarrow> bool" 
where
  "pertenece Leaf x         = False" 
| "pertenece (Node i a d) x = 
    (if x < a then pertenece i x else
     if x > a then pertenece d x
     else True)"

value "pertenece abb1 3"
lemma "pertenece abb1 3 = True" by simp
value "pertenece abb1 5"
lemma "pertenece abb1 5 = False" by simp
   
text {* (inserta x t) es el ABB obtenido insertando el elemento x en el
  ABB t. Por ejemplo, 
     inserta 4 abb1 = \<langle>\<langle>\<rangle>, 3, \<langle>\<langle>\<langle>\<rangle>, 4, \<langle>\<rangle>\<rangle>, 9, \<langle>\<rangle>\<rangle>\<rangle>
     inserta 2 abb1 = \<langle>\<langle>\<langle>\<rangle>, 2, \<langle>\<rangle>\<rangle>, 3, \<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>\<rangle>
     inserta 12 abb1 = \<langle>\<langle>\<rangle>, 3, \<langle>\<langle>\<rangle>, 9, \<langle>\<langle>\<rangle>, 12, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>
*}
fun inserta :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" 
where
  "inserta x Leaf = Node Leaf x Leaf" 
| "inserta x (Node l a r) =
    (if x < a then Node (inserta x l) a r else
     if x > a then Node l a (inserta x r)
     else Node l a r)"

value "inserta 4 abb1"
lemma "inserta 4 abb1 = \<langle>\<langle>\<rangle>, 3, \<langle>\<langle>\<langle>\<rangle>, 4, \<langle>\<rangle>\<rangle>, 9, \<langle>\<rangle>\<rangle>\<rangle>" by simp
value "inserta 2 abb1"
lemma "inserta 2 abb1 = \<langle>\<langle>\<langle>\<rangle>, 2, \<langle>\<rangle>\<rangle>, 3, \<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>\<rangle>" by simp
value "inserta 12 abb1"
lemma "inserta 12 abb1 = \<langle>\<langle>\<rangle>, 3, \<langle>\<langle>\<rangle>, 9, \<langle>\<langle>\<rangle>, 12, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>" by simp

subsection "Corrección funcional"

text {* Prop: Si t es un ABB, entonces son equivalentes:
  · La relación (pertenece t x) se verifica 
  · x pertenece al conjunto de los elementos de t. *}
lemma set_tree_pertenece: 
  "bst t \<Longrightarrow> pertenece t x = (x \<in> set_tree t)"
apply (induction t)
apply auto
done

text {* Prop.: El conjunto de los elementos de (inserta x t) es igual a
  la unión de {x} y el conjunto de los elementos de t. *}
lemma set_tree_inserta: 
  "set_tree (inserta x t) = {x} \<union> set_tree t"
apply (induction t)
apply auto
done

subsection "Conservación del invariante"

text {* Prop: Al insertar un elemento en un ABB se obtiene un ABB. *}
lemma bst_inserta: 
  "bst t \<Longrightarrow> bst (inserta x t)"
apply (induction t)
apply (auto simp: set_tree_inserta)
done

section "Reducción del número de comparaciones"

text\<open>Idea: never test for \<open>=\<close> but remember the last value where you
should have tested for \<open>=\<close> but did not. Compare with that value when
you reach a leaf.\<close>

fun pertenece2 :: "('a::linorder) tree \<Rightarrow> 'a option \<Rightarrow> 'a \<Rightarrow> bool" 
where
  "pertenece2 Leaf z x = 
    (case z of None   \<Rightarrow> False 
             | Some y \<Rightarrow> x = y) " 
| "pertenece2 (Node l a r) z x =
    (if x < a 
     then pertenece2 l z x 
     else pertenece2 r (Some a) x)"

lemma pertenece2_Some:
  "\<lbrakk> bst t
   ; \<forall>x \<in> set_tree t. y < x \<rbrakk>
  \<Longrightarrow> pertenece2 t (Some y) x = (pertenece t x \<or> x=y)"
apply (induction t arbitrary: y)
apply auto
done

lemma pertenece2_None:
  "bst t \<Longrightarrow> pertenece2 t None x = pertenece t x"
apply (induction t)
apply (auto simp: pertenece2_Some)
done

section "Árboles con información del tamaño"

text {* Un árbol con información de tamaño es un árbol cuyos elementos
  son pares donde la segunda componente es un número natural (que
  representa el tamaño). *}
type_synonym 'a tree_sz = "('a * nat) tree"

text {* (inv_sz t) se verifica si t es un árbol con información de
  tamaño. *} 
fun inv_sz :: "('a::linorder) tree_sz \<Rightarrow> bool" 
where
  "inv_sz \<langle>\<rangle> = True" 
| "inv_sz \<langle>l, (a,s), r\<rangle> = 
    (inv_sz l \<and> inv_sz r \<and> s = size l + size r + 1)"

text {* (sz t) es el tamaño del árbol con información de tamaño t. *}    
fun sz :: "'a tree_sz \<Rightarrow> nat" 
where
  "sz Leaf             = 0" 
| "sz (Node _ (_,s) _) = s"

text {* (un_sz t) es el árbol sin información de tamaño correspondiente
  al árbol con información de tamaño t. *}
abbreviation un_sz :: "'a tree_sz \<Rightarrow> 'a tree" 
where
  "un_sz t \<equiv> map_tree fst t"

text {* (ins_sz x t) es el ABB con información de tamaño obtenido
  insertando el elemento x en el ABB con información de tamaño t. *}
fun ins_sz :: "'a::linorder \<Rightarrow> 'a tree_sz \<Rightarrow> 'a tree_sz" 
where
  "ins_sz x Leaf = Node Leaf (x,1) Leaf" 
| "ins_sz x (Node l (a,s) r) =
    (if x < a 
       then let l' = ins_sz x l in Node l' (a, sz l' + sz r + 1) r 
     else if x > a 
       then let r' = ins_sz x r in Node l (a, sz l + sz r' + 1) r'
     else Node l (a,s) r)"

subsection "Corrección funcional"

text {* El árbol sin información de tamaño obtenido insertado x en t es
  igual que árbol obtenido insertando x en el árbol sin información de
  tamaño correspondiente a t. *}
lemma un_sz_ins_sz: 
  "un_sz (ins_sz x t) = inserta x (un_sz t)"
apply (induction t)
apply auto
done

subsection "Conservación del invariante"

text{* Sea t un árbol con información de tamaño. Si el árbol sin
  información de tamaño correspondiente a t es un ABB, entonces también
  los es el árbol sin información de tamaño correspondiente a insertar
  un elemento en t. *}
lemma "bst (un_sz t) \<Longrightarrow> bst (un_sz (ins_sz x t))"
by (simp add: un_sz_ins_sz bst_inserta)

text {* Para los árboles con información de tamaño las funciones six y
  size son equivalentes. *}
lemma sz_size [simp]: 
  "inv_sz t \<Longrightarrow> sz t = size t"
apply (induction t)
apply auto
done

text {* Al insertar un elemento en un árbol con información de tamaño se
  obtiene otro árbol con información de tamaño. *}
lemma "inv_sz t \<Longrightarrow> inv_sz (ins_sz x t)"
apply (induction t)
apply (auto)
done

text {* (nth_min t n) es el n-ésimo elemento del árbol con información
  de tamaño t (con los elementos ordenado de manera creciente). *}
fun nth_min :: "('a::linorder) tree_sz \<Rightarrow> nat \<Rightarrow> 'a" where
"nth_min \<langle>l, (a,s), r\<rangle> n =
   (let sl = sz l in
    if n = sl then a else
    if n < sl then nth_min l n 
              else nth_min r (n-sl-1))"

text {* Si t es un árbol con información de tamaño tal que su
  correspondiente árbol sin información de tamaño es un ABB y n es menor
  que el tamaño de t, entonces (nth_min t n) es el n-ésimo elemento del
  recorrido inorden del árbol sin información de tamaño correspondiente
  a t. *}              
lemma "\<lbrakk> bst (un_sz t)
       ; inv_sz t
       ; n < size t \<rbrakk>
       \<Longrightarrow> nth_min t n = nth (inorder (un_sz t)) n"
apply (induction t arbitrary: n)
apply (auto simp: nth_append)
done

text {* En el lema anterior se puede eliminar la primera hipótesis. *}
lemma "\<lbrakk> inv_sz t
       ;  n < size t \<rbrakk>
       \<Longrightarrow> nth_min t n = nth (inorder (un_sz t)) n"
apply (induction t arbitrary: n)
apply (auto simp: nth_append)
done

section "Compressing the Height of BSTs"

fun compress :: "'a tree \<Rightarrow> 'a tree" where
"compress (Node Leaf a t) =
  (case compress t of
     Node Leaf b u \<Rightarrow> Node (Node Leaf a Leaf) b u |
     u \<Rightarrow> Node Leaf a u)" |
"compress (Node l a r) = Node (compress l) a (compress r)" |
"compress Leaf = Leaf"

(* Another way of saying that \<open>bst\<close> and \<open>set_tree\<close> are preserved: *)
lemma "inorder(compress t) = inorder t"
apply(induction t rule: compress.induct)
apply (auto split: tree.split)
done

lemma "height (compress t) \<le> height t"
apply(induction t rule: compress.induct)
apply (auto split: tree.split)
done

(* What is the correct relationship? *)
lemma "height t \<le> height (compress t)"
oops


section "BST Implementation of Maps"

fun lookup :: "('a::linorder * 'b) tree \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup Leaf x = None" |
"lookup (Node l (a,b) r) x =
  (if x < a then lookup l x else
   if x > a then lookup r x
   else Some b)"

fun update :: "'a \<Rightarrow> 'b \<Rightarrow> ('a::linorder * 'b) tree \<Rightarrow> ('a * 'b) tree" where
"update x y Leaf = Node Leaf (x,y) Leaf" |
"update x y (Node l (a,b) r) =
  (if x < a then Node (update x y l) (a,b) r else
   if x > a then Node l (a,b) (update x y r)
   else Node l (x,y) r)"

subsection "Functional Correctness"

lemma "lookup (update x y t) a = (if x=a then Some y else lookup t a)"
apply(induction t)
apply auto
done

subsection "Preservation of Invariant"

definition "bst1 t = bst (map_tree fst t)"

lemma map_tree_update: "map_tree fst (update x y t) = inserta x (map_tree fst t)"
apply(induction t)
apply auto
done

lemma "bst1 t \<Longrightarrow> bst1(update x y t)"
apply(induction t)
apply (auto simp: bst1_def map_tree_update set_tree_inserta)
done

end
