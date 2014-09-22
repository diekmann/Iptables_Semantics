theory jiraver254
imports "../CTranslation"
begin

install_C_file "jiraver254.c"

context jiraver254
begin

thm f_body_def
thm g_body_def
thm h_body_def
thm ptrconversion_body_def

end

end


