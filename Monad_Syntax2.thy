theory Monad_Syntax2
  imports Monad_Syntax
begin

abbreviation (do_notation)
  bind_do2 :: "['a, 'b \<Rightarrow> 'c] \<Rightarrow> 'c"
  where "bind_do2 \<equiv> bind_do"

syntax
  "_do_block_typ" :: "type_name \<Rightarrow> do_binds \<Rightarrow> 'a" ("do _ {//(2  _)//}" [12] 62)
  "_bind_do_typ" :: "type_name \<Rightarrow> 'a"

syntax "" :: "logic \<Rightarrow> type_name" ("@_") (* needed to enter the translations below *)

translations
  "_do_block_typ T (_do_cons (_do_then t) (_do_final e))"
    \<rightharpoonup> "_bind_do_typ T t (\<lambda>_. e)"
  "_do_block_typ T (_do_cons (_do_bind p t) (_do_final e))"
    \<rightharpoonup> "_bind_do_typ T t (\<lambda>p. e)"
  "_do_block_typ T (_do_cons (_do_let p t) bs)"
    \<rightharpoonup> "let p = t in _do_block_typ T bs"
  "_do_block_typ T (_do_cons b (_do_cons c cs))"
    \<rightharpoonup> "_do_block_typ T (_do_cons b (_do_final (_do_block_typ T (_do_cons c cs))))"
  "_do_block_typ T (_do_final e)" \<rightharpoonup> "e :: (_ @T)"
  "_bind_do_typ T" \<rightharpoonup> "CONST bind_do2 :: (_ @T \<Rightarrow> (_ \<Rightarrow> _ @T) \<Rightarrow> _ @T)"

no_syntax "" :: "logic \<Rightarrow> type_name" ("@_") (* removing temporary syntax again *)

type_synonym 'a olist = "'a option list"
axiomatization bind_olist :: "'a olist \<Rightarrow> ('a \<Rightarrow> 'b olist) \<Rightarrow> 'b olist"
adhoc_overloading bind bind_olist

term "do list { c<-y; return (c*c) }"

