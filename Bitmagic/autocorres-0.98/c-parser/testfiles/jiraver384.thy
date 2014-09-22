theory jiraver384
  imports "../CTranslation"
begin

  install_C_file "jiraver384.c"

  context jiraver384
  begin
  thm foo_body_def
  end
  
end
