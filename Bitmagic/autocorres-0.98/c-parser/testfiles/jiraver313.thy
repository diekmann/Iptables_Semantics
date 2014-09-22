theory jiraver313
  imports "../CTranslation"
begin

ML {* Feedback.verbosity_level := 6 *}

install_C_file memsafe "jiraver313.c"

ML {*
local
open Absyn
val (decls, _) = StrictCParser.parse 15 [] (IsarInstall.mk_thy_relative @{theory} "jiraver313.c");
in
val Decl d = hd decls
val VarDecl vd = RegionExtras.node d
end
*}

context jiraver313
begin
term foo
term bar
thm f_body_def
thm g_body_def

end

end
