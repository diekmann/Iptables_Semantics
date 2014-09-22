theory jiraver400
  imports "../CTranslation"
begin

  install_C_file "jiraver400.c" [machinety=bool,roots=[h,indep1]]

context jiraver400
begin

  thm f_body_def
  thm indep1_body_def

end

end
