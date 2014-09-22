theory postfixOps
imports "../CTranslation"
begin

install_C_file "postfixOps.c"

context "postfixOps"
begin

thm doit_body_def


end (* context *)


end
