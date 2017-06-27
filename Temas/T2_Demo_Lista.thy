theory T2_Demo_Lista
imports Main
begin

section {* El tipo de las listas *}

text {* ('a list) es el tipo de las listas con elementos de tipo 'a *}
datatype 'a lista = Nil | Cons "'a" "'a lista"

text {* Ejemplos de inferencia de tipo. *}
term "Nil"        (* da "lista.Nil" :: "'a lista" *)
term "Cons 1 Nil" (* da "lista.Cons 1 lista.Nil" :: "'a lista" *)

text {* Declaración para acortar los nombres. *}
declare [[names_short]]

text {* Ejemplos de inferencia de tipo con nombres acortados. *}
term "Nil"        (* da "Nil" :: "'a lista" *)
term "Cons 1 Nil" (* da "Cons 1 lista.Nil" :: "'a lista" *)

section {* Funciones sobre listas: conc e inversa *}

text {* (conc xs ys) es la concatenación de las listas xs e ys. Por
  ejemplo,   
     conc (Cons a (Cons b Nil)) (Cons c (Cons d Nil))
     = Cons a (Cons b (Cons c (Cons d Nil)))
*}
fun conc :: "'a lista \<Rightarrow> 'a lista \<Rightarrow> 'a lista" 
where
  "conc Nil ys         = ys" 
| "conc (Cons x xs) ys = Cons x (conc xs ys)"

value "conc (Cons a (Cons b Nil)) (Cons c (Cons d Nil))"
lemma "conc (Cons a (Cons b Nil)) (Cons c (Cons d Nil))
       = Cons a (Cons b (Cons c (Cons d Nil)))" by simp
       
text {* (inversa xs) es la inversa de la lista xs. Por ejemplo,  
*}
fun inversa :: "'a lista \<Rightarrow> 'a lista" 
where
  "inversa Nil         = Nil" 
| "inversa (Cons x xs) = conc (inversa xs) (Cons x Nil)"

value "inversa (Cons a (Cons b (Cons c Nil)))"
lemma "inversa (Cons a (Cons b (Cons c Nil)))
       = Cons c (Cons b (Cons a Nil))" by simp

section {* Ejemplo de búsqueda descendente de la demostración *}

text {* El objetivo de esta sección es mostrar cómo se conjeturan lemas
  auxiliares para la demostración de la idempotencia de la función
  inversa.
  
  Se mostrarán cómo los errores de las pruebas ayudan a conjeturar los
  lemas.
*}
       
text {* Primer intento de prueba de inversa_inversa. *}
theorem inversa_inversa_1: 
  "inversa (inversa xs) = xs"
apply (induction xs)
apply auto
oops

text {* Queda sin demostrar el siguiente objetivo:
     inversa (inversa xs) = xs \<Longrightarrow> 
     inversa (conc (inversa xs) (Cons x1 Nil)) = Cons x1 xs
            
  Se observa que contiene la expresión 
     inversa (conc (inversa xs) (Cons x1 Nil))
  que se puede simplificar a 
     conc (Cons x1 Nil) (inversa (inversa xs)) 
  con el siguiente lema:
     inversa (conc xs ys) = conc (inversa ys) (inversa xs)
*}

text {* Primer intento de prueba de inversa_conc. *}
lemma inversa_conc_1: 
  "inversa (conc xs ys) = conc (inversa ys) (inversa xs)"
apply (induction xs)
apply auto
oops

text {* Queda sin demostrar el objetivo
     inversa ys = conc (inversa ys) Nil
  Se puede demostrar con el siguiente lema
     conc xs Nil = xs
*}

text {* Prueba de conc_Nil2. *}
lemma conc_Nil2: 
  "conc xs Nil = xs"
apply (induction xs)
apply auto
done

text {* Segundo intento de prueba de inversa_conc usando conc_Nil2. *}
lemma inversa_conc_2: 
  "inversa (conc xs ys) = conc (inversa ys) (inversa xs)"
apply (induction xs)
apply (auto simp add: conc_Nil2)
oops

text {* Queda sin probar el objetivo
     inversa (conc xs ys) = conc (inversa ys) (inversa xs) \<Longrightarrow>
       conc (conc (inversa ys) (inversa xs)) (Cons x1 Nil) =
       conc (inversa ys) (conc (inversa xs) (Cons x1 Nil))
  que se puede simplificar usando la propiedad asociativa de conc.       
*}

text {* Prueba de asociatividad de conc. *}
lemma conc_asoc: 
  "conc (conc xs ys) zs = conc xs (conc ys zs)"
apply (induction xs)
apply auto
done

text {* Prueba de inversa_conc usando conc_Nil2 y conc_asoc. *}
lemma inversa_conc: 
  "inversa (conc xs ys) = conc (inversa ys) (inversa xs)"
apply (induction xs)
apply (auto simp add: conc_Nil2 conc_asoc)
done

text {* Prueba de inversa_inversa usando inversa_conc. *}
theorem inversa_inversa: 
  "inversa (inversa xs) = xs"
apply (induction xs)
apply (auto simp add: inversa_conc)
done

text {* Una vez encontrada la demostración, se puede modificar la
  presentación declarando los lemas como reglas de simplificación, como
  se muestra a continuación. *} 

lemma conc_Nil2' [simp]: 
  "conc xs Nil = xs"
by (induction xs) auto

lemma conc_asoc' [simp]: 
  "conc (conc xs ys) zs = conc xs (conc ys zs)"
by (induction xs) auto

lemma inversa_conc' [simp]: 
  "inversa (conc xs ys) = conc (inversa ys) (inversa xs)"
by (induction xs) auto

theorem inversa_inversa': 
  "inversa (inversa xs) = xs"
by (induction xs) auto

end
