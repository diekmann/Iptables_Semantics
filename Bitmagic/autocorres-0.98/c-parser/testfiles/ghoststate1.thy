theory ghoststate1
imports "../CTranslation"
begin

install_C_file "simple_annotated_fn.c" [ghostty="nat \<Rightarrow> nat"]

(* demonstrates existence of ghost'state global variable of appropriate type *)
term "\<acute>ghost'state :== (\<lambda>x. x + (1::nat))"

end
