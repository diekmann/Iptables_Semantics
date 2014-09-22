theory jiraver54
imports "../CTranslation"
begin

install_C_file "jiraver54.c"

context jiraver54
begin

thm f_body_def
thm f_modifies

end (* context *)


end
