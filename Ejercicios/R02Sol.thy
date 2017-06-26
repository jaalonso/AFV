theory R02Sol

imports Complex_Main
begin

text {* Relación 2 *}

text {* 
  ----------------------------------------------------------------------
  Ejercicio 1.1. [Plegados sobre árboles]
  
  Definir el tipo de dato arbolH para representar los árboles binarios
  que sólo tienen valores en las hojas. Por ejemplo, el árbol
       ·
      / \
     3   ·
        / \
       5   7
  se representa por
     Nodo (Hoja 3) (Nodo (Hoja 5) (Hoja 7))
  ------------------------------------------------------------------- *}

datatype 'a arbolH = 
  Hoja 'a 
| Nodo "'a arbolH" "'a arbolH"

abbreviation ejArbolH1 :: "int arbolH" 
where
  "ejArbolH1 \<equiv> Nodo (Hoja (3::int)) (Nodo (Hoja 5) (Hoja 7))"

text {*
  ----------------------------------------------------------------------
  Ejercicio 1.2. Definir la función
     infijo :: "'a arbolH \<Rightarrow> 'a list" 
  tal que (infijo x) es el recorrido infijo del árbol hoja x. Por
  ejemplo,
     infijo ejArbolH1 = [3,5,7]
  ------------------------------------------------------------------- *}

fun infijo :: "'a arbolH \<Rightarrow> 'a list" 
where
  "infijo (Hoja x)   = [x]"
| "infijo (Nodo i d) = infijo i @ infijo d"  

value "infijo ejArbolH1"
lemma "infijo ejArbolH1 = [3,5,7]" by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 1.3. Consultar la definición de la función fold de plegado
  de listas.
  ------------------------------------------------------------------- *}

-- "Una forma de consultarlo es"  
thm fold.simps  

text {*
  El resultado es   
     fold ?f []         = id
     fold ?f (?x # ?xs) = fold ?f ?xs \<circ> ?f ?x
  *}

-- "Otra forma de consultarlo es"  
thm fold_simps

text {*
  El resultado es
     fold ?f [] ?s         = ?s
     fold ?f (?x # ?xs) ?s = fold ?f ?xs (?f ?x ?s)
  *}

-- "Se puede comprobar la definición"  
lemma 
  "fold f [] s     = s"
  "fold f (x#xs) s = fold f xs (f x s)" 
by simp_all

text {*
  ----------------------------------------------------------------------
  Ejercicio 1.4. Definir la función
     fold_arbolH :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a arbolH \<Rightarrow> 'b \<Rightarrow> 'b"
  tal que (fold_arbolH f x y) es plegado del árbol hoja x con la
  operación f y el valor inicial x. Por ejemplo,
     fold_arbolH op+ ejArbolH1 0 = 15
     fold_arbolH op* ejArbolH1 1 = 105
  ------------------------------------------------------------------- *}
  
fun fold_arbolH :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a arbolH \<Rightarrow> 'b \<Rightarrow> 'b" 
where
  "fold_arbolH f (Hoja x) y   = f x y"
| "fold_arbolH f (Nodo i d) y = fold_arbolH f d (fold_arbolH f i y)"

value "fold_arbolH op+ ejArbolH1 0"
lemma "fold_arbolH op+ ejArbolH1 0 = 15" by simp
value "fold_arbolH op* ejArbolH1 1"
lemma "fold_arbolH op* ejArbolH1 1 = 105" by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 1.5. Demostrar que
     fold_arbolH f x y = fold f (infijo x) y
  ------------------------------------------------------------------- *}

lemma "fold_arbolH f x y = fold f (infijo x) y"  
by (induction x arbitrary: y) auto

text {*
  ----------------------------------------------------------------------
  Ejercicio 1.6. Definir la función
     espejo :: "'a arbolH \<Rightarrow> 'a arbolH"
  tal que (espejo x) es la imagen especular del árbol x. Por ejemplo,
     espejo ejArbolH1 = Nodo (Nodo (Hoja 7) (Hoja 5)) (Hoja 3)
  ------------------------------------------------------------------- *}

fun espejo :: "'a arbolH \<Rightarrow> 'a arbolH" 
where
  "espejo (Hoja x)   = Hoja x"  
| "espejo (Nodo i d) = Nodo (espejo d) (espejo i)"

value "espejo ejArbolH1"
lemma "espejo ejArbolH1 = Nodo (Nodo (Hoja 7) (Hoja 5)) (Hoja 3)" 
  by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 1.7. Demostrar que
     infijo (espejo t) = rev (infijo t)
  ------------------------------------------------------------------- *}
    
lemma "infijo (espejo t) = rev (infijo t)"  
by (induction t) auto
    
text {*
  ----------------------------------------------------------------------
  Ejercicio 2.1. [Alineamientos de lista]
  Un alineamiento de dos lista xs e ys es una lista cuyos elementos son
  los de xs e ys consevando su orden original. Por ejemplo, un
  alineamiento de [a,b] y [c,d,e] es [a,c,d,b,e] y otro es [c,a,d,e,b].
  
  Definir la función
     alineamientos :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" 
  tal que (alineamientos xs ys) es la lista de los alineamientos de xs e
  ys. Por ejemplo, 
     alineamientos [a,b] [c,d,e] 
     = [[a,b,c,d,e],[a,c,b,d,e],[a,c,d,b,e],[a,c,d,e,b],[c,a,b,d,e],
        [c,a,d,b,e],[c,a,d,e,b],[c,d,a,b,e],[c,d,a,e,b],[c,d,e,a,b]]
  ------------------------------------------------------------------- *}

fun alineamientos :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list"  
where
  "alineamientos xs []         = [xs]"
| "alineamientos [] ys         = [ys]"  
| "alineamientos (x#xs) (y#ys) = 
    map (op # x) (alineamientos xs (y#ys)) @ 
    map (op # y) (alineamientos (x#xs) ys)"  
   
value "alineamientos [a,b] [c,d,e]"
lemma "alineamientos [a,b] [c,d,e] =
       [[a,b,c,d,e],[a,c,b,d,e],[a,c,d,b,e],[a,c,d,e,b],[c,a,b,d,e],
        [c,a,d,b,e],[c,a,d,e,b],[c,d,a,b,e],[c,d,a,e,b],[c,d,e,a,b]]"
  by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.2. Demostrar que la longitud de cualquier alineamiento de
  las listas xs e ys es la suma de las longitudes de los alineamientos
  de xs e ys.
  ------------------------------------------------------------------- *}

lemma "zs \<in> set (alineamientos xs ys) \<Longrightarrow> 
       length zs = length xs + length ys"
apply (induction xs ys arbitrary: zs rule: alineamientos.induct)
apply auto  
done  

text {* Nota. La función set convierte una lista en el conjunto de sus
  elementos. Por ejemplo, el resultado de
     value "set [a,b,c]"
  es   
     "{a, b, c}"
      :: "'a set"
  *}

text {*
  ----------------------------------------------------------------------
  Ejercicio 3.1. [Plegado de listas]
  
  Definir, por recursión, la función
     suma1 :: "int list \<Rightarrow> int" 
  tal que (suma1 xs) es la suma de los elementos de la lista xs. Por
  ejemplo, 
     suma1 [3,1,4] = 8
  ------------------------------------------------------------------- *}
  
fun suma1 :: "int list \<Rightarrow> int" 
where
  "suma1 []     = 0"
| "suma1 (x#xs) = x + suma1 xs"  

value "suma1 [3,1,4]"
lemma "suma1 [3,1,4] = 8" by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 3.2. Definir, por plegado, la función
     suma2 :: "int list \<Rightarrow> int" 
  tal que (suma2 xs) es la suma de los elementos de la lista xs. Por
  ejemplo, 
     suma2 [3,1,4] = 8
  ------------------------------------------------------------------- *}
  
definition suma2 :: "int list \<Rightarrow> int" 
where 
  "suma2 xs \<equiv> fold op+ xs 0"

text {*
  ----------------------------------------------------------------------
  Ejercicio 3.3. Demostrar que las funciones suma1 y suma2 son
  equivalentes.
  ------------------------------------------------------------------- *}

lemma aux: "fold op+ xs a = suma1 xs + a"  
by (induction xs arbitrary: a) auto
  
lemma "suma1 xs = suma2 xs"
by (simp add: aux suma2_def)

text {*
  ----------------------------------------------------------------------
  Ejercicio 4.1. [Lista con elementos distintos]
  
  Definir, por recursión, la función
     pertenece :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" 
  tal que (pertenece x ys) se verifica si x es un elemento de ys. Por
  ejemplo, 
     pertenece 2 [7,2,5] = True
     pertenece 4 [7,2,5] = False
  ------------------------------------------------------------------- *}

fun pertenece :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" 
where
  "pertenece x []     = False"
| "pertenece x (y#ys) = (x = y \<or> pertenece x ys)"

value "pertenece 4 [7,2,(5::nat)]"
lemma "pertenece 4 [7,2,(5::nat)] = False" by simp
value "pertenece 2 [7,2,(5::nat)]"
lemma "pertenece 2 [7,2,(5::nat)] = True" by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 4.2. Definir la función
     distintos :: "'a list \<Rightarrow> bool
  tal que (distintos xs) se verifica si la lista xs no tiene elementos
  repetidos. Por ejemplo, 
     distintos [7,2,5] = True
     distintos [7,2,7] = False
  ------------------------------------------------------------------- *}

fun distintos :: "'a list \<Rightarrow> bool" 
where
  "distintos []     = True"
| "distintos (x#xs) = (\<not>(pertenece x xs) \<and> distintos xs)"

value "distintos [7,2,(5::nat)]"
lemma "distintos [7,2,(5::nat)] = True" by simp
value "distintos [7,2,(7::nat)]"
lemma "distintos [7,2,(7::nat)] = False" by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 4.3. Demostrar que la inversa de una lista no tiene
  repeticiones si, y sólo si, la lista original no tiene repeticiones. 
  ------------------------------------------------------------------- *}

lemma pertenece_conc:
  "pertenece x (ys @ zs) = (pertenece x ys \<or> pertenece x zs)"
by (induction ys) simp_all

lemma pertenece_rev:
  "pertenece x (rev ys) = pertenece x ys"
by (induction ys) (auto simp add: pertenece_conc)

lemma distintos_conc:
  "distintos (xs @ [y]) = ( \<not>(pertenece y xs) \<and> distintos xs)"
by (induction xs) (auto simp add: pertenece_conc)  

lemma "distintos (rev xs) = distintos xs"
by (induction xs) (auto simp add: distintos_conc pertenece_rev)

text {*
  ----------------------------------------------------------------------
  Ejercicio 5.1. [Plegados de listas por la derecha y por la izquierda]
  
  Consultar las definidiciones de fold y foldr
  ------------------------------------------------------------------- *}

thm fold.simps
thm foldr.simps

text {*
  El resultado es
    fold ?f []         = id
    fold ?f (?x # ?xs) = fold ?f ?xs \<circ> ?f ?x
    
    foldr ?f []         = id
    foldr ?f (?x # ?xs) = ?f ?x \<circ> foldr ?f ?xs
*}

lemma "fold  f [a,b,c] d = f c (f b (f a d))" by simp
lemma "foldr f [a,b,c] d = f a (f b (f c d))" by simp

lemma "foldr (op-) [1,2,3::int] 7 = (1 - (2 - (3 - 7)))" by auto
lemma "fold  (op-) [1,2,3::int] 7 = 3 - (2 - (1 - 7)) " by auto

text {*
  ----------------------------------------------------------------------
  Ejercicio 5.2. Definir, usando fold, la función
     longitud1 :: "'a list \<Rightarrow> nat" 
  tal que (longitud1 xs) es la longitud de la lista xs. Por ejemplo,
     longitud1 [a,b,c] = 3
  ------------------------------------------------------------------- *}

definition longitud1 :: "'a list \<Rightarrow> nat" 
where
  "longitud1 xs = fold (\<lambda>x. Suc) xs 0"

value "longitud1 [a,b,c]"  
lemma "longitud1 [a,b,c] = 3" by (simp add: longitud1_def)  
  
text {*
  ----------------------------------------------------------------------
  Ejercicio 5.3. Definir, usando fold, la función
     longitud2 :: "'a list \<Rightarrow> nat" 
  tal que (longitud2 xs) es la longitud de la lista xs. Por ejemplo,
     longitud2 [a,b,c] = 3
  ------------------------------------------------------------------- *}

definition longitud2 :: "'a list \<Rightarrow> nat" 
where
  "longitud2 xs = foldr (\<lambda>x. Suc) xs 0"
  
value "longitud2 [a,b,c]"  
lemma "longitud2 [a,b,c] = 3" by (simp add: longitud2_def)  

text {*
  ----------------------------------------------------------------------
  Ejercicio 5.4. Demostrar que las funciones longitud1 y length son
  equivalentes.
  ------------------------------------------------------------------- *}

lemma aux_fold:
  "fold (\<lambda>x. Suc) xs y  = y + length xs"
by (induction xs arbitrary: y) auto

lemma "longitud1 xs = length xs"
by (simp add: longitud1_def aux_fold)

text {*
  ----------------------------------------------------------------------
  Ejercicio 5.5. Demostrar que las funciones longitud2 y length son
  equivalentes.
  ------------------------------------------------------------------- *}

lemma aux_foldr:
  "foldr (\<lambda>x. Suc) xs y  = y + length xs"
by (induction xs arbitrary: y) auto

lemma "longitud2 xs = length xs"
by (simp add: longitud2_def aux_foldr)

text {*
  ----------------------------------------------------------------------
  Ejercicio 6.1. [Cortes de listas]
  
  Dada una lista xs, el corte de xs de longitud menor o igual que m con
  inicio en i es la lista formada por el elemento de xs en la posición i
  y en las m-1 siguientes posiciones (si existen dichos elementos). 
  
  Definir la función
     corte :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
  tal que (corte xs i m) es el corte de xs de longitud menor o igual que
  m que empieza en la posición i. Por ejemplo, 
     "corte [0,1,2,3,4,5,6] 2 3 = [2,3,4] 
     "corte [0,1,2,3,4,5,6] 2 9 = [2,3,4,5,6] 
     "corte [0,1,2,3,4,5,6] 9 9 = []
  ------------------------------------------------------------------- *}

definition corte :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
where
  "corte xs i m = take m (drop i xs)"

declare corte_def [simp]
  
lemma "corte [0,1,2,3,4,5,6 ::int] 2 3 = [2,3,4]" by simp
lemma "corte [0,1,2,3,4,5,6 ::int] 2 9 = [2,3,4,5,6]" by simp 
lemma "corte [0,1,2,3,4,5,6 ::int] 9 9 = []" by simp
  
text {*
  ----------------------------------------------------------------------
  Ejercicio 6.2. Demostrar que la concatenación de dos cortes adyacentes
  se puede expresar como un único corte.
  ------------------------------------------------------------------- *}

lemma "corte xs i m1 @ corte xs (i + m1) m2 = corte xs i (m1 + m2)"
by (induction xs) (auto simp add: take_add add.commute)

text {*
  Los lemas utilizados son
  + take_add:    take (i + j) xs = take i xs @ take j (drop i xs)
  + add.commute: a + b = b + a
*}

text {*
  ----------------------------------------------------------------------
  Ejercicio 6.3. Demostrar que los cortes en listas de elementos no
  repetidos no tienen elementos repetidos.
  ------------------------------------------------------------------- *}

lemma pertenece_take:
  "pertenece a (take n xs) \<Longrightarrow> pertenece a xs"
by (metis append_take_drop_id pertenece_conc)
 
lemma distintos_take:
  "distintos xs \<Longrightarrow> distintos (take n xs)"
apply (induction xs arbitrary: n)
apply simp
apply (case_tac n)
  apply (auto simp add: pertenece_take)
done

lemma pertenece_drop:
  "pertenece a (drop n xs) \<Longrightarrow> pertenece a xs"
by (metis append_take_drop_id pertenece_conc)

lemma distintos_drop:
  "distintos xs \<Longrightarrow> distintos (drop n xs)"
apply (induction xs arbitrary: n)
apply simp
apply (case_tac n)
  apply (auto simp add: pertenece_drop)
done
  
lemma "distintos xs \<Longrightarrow> distintos (corte xs i m)"
by (induct xs) (auto simp add: distintos_take distintos_drop)

end

