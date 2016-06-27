theory NumberWang_IPv4
imports Main
  "~~/src/HOL/Word/Word"
begin

section\<open>Helper Lemmas for Low-Level Operations on Machine Words\<close>
text\<open>Needed for IPv4 Syntax\<close>

lemma mod256: "((d::nat) + 256 * c + 65536 * b + 16777216 * a) mod 256 = d mod 256"
proof -
  from mod_mult_self2[where a="d + 256 * c + 65536 * b" and b="256" and c="65536 * a"] have 
    "(d + 256 * c + 65536 * b + 256 * 65536 * a) mod 256 = (d + 256 * c + 65536 * b) mod 256"
    by simp
  also have "\<dots>  = (d + 256 * c) mod 256"
    using mod_mult_self2[where a="d + 256 * c" and b="256" and c="256 * b"] by simp
  also have "\<dots> = d mod 256" using mod_mult_self2 by blast
  finally show ?thesis by presburger
qed

lemma div65536: assumes "a < 256" "b < 256" "c < 256" "d < 256" 
    shows "nat ((int d + int (256 * c) + int (65536 * b) + int (16777216 * a)) div 65536 mod 256) = b"
proof -
  from zdiv_mult_self[where a="int d + int (256 * c) + int (65536 * b)" and m=65536 and n="256 * (int a)"] have
    "(int d + int (256 * c) + int (65536 * b) + int (16777216 * a)) div 65536 =
     ((int d + int (256 * c) + int (65536 * b)) div 65536) + 256 * int a" by linarith
  also from zdiv_mult_self[where a="int d + int (256 * c)" and m="65536" and n="int b"] have
    "\<dots> = (int d + int (256 * c)) div 65536 + int b + 256 * int a" by linarith
  also from assms have "\<dots> = int b + 256 * int a" by simp
  finally have helper:
    "(int d + int (256 * c) + int (65536 * b) + int (16777216 * a)) div 65536 = int b + 256 * int a" .
  from assms show ?thesis
    unfolding helper
    apply(simp)
    apply(subst mod_pos_pos_trivial)
      apply simp_all
    done
qed

lemma div256: assumes "a < 256" "b < 256" "c < 256" "d < 256" 
  shows "nat ((int d + int (256 * c) + int (65536 * b) + int (16777216 * a)) div 256 mod 256) = c"
proof -
  from zdiv_mult_self[where a="int d + int (256 * c) + int (65536 * b)" and m=256 and n="65536 * (int a)"] have
    "(int d + int (256 * c) + int (65536 * b) + int (16777216 * a)) div 256 =
     ((int d + int (256 * c) + int (65536 * b)) div 256) + 65536 * int a" by linarith
  also from zdiv_mult_self[where a="int d + int (256 * c)" and m="256" and n="256 * int b"] have
    "\<dots> = (int d + int (256 * c)) div 256 + 256 * int b + 65536 * int a" by linarith
  also from zdiv_mult_self[where a="int d" and m="256" and n="int c"] have
    "\<dots> = (int d) div 256 + int c + 256 * int b + 65536 * int a" by linarith
  also from assms have "\<dots> = int c + 256 * int b + 65536 * int a" by simp
  finally have helper1: "(int d + int (256 * c) + int (65536 * b) + int (16777216 * a)) div 256 =
                          int c + 256 * int b + 65536 * int a" .
  
  from mod_mult_self2[where a="int c + 256 * int b" and c="256 * int a" and b=256] have 
    "(int c + 256 * int b + 65536 * int a) mod 256 = (int c + 256 * int b) mod 256" by simp
  also have "\<dots> = int c mod 256" using mod_mult_self2[where a="int c" and b=256 and c="int b"] by simp
  also have "\<dots> = int c" using assms
    apply(subst mod_pos_pos_trivial)
    by(simp_all)
  finally have helper2: "(int c + 256 * int b + 65536 * int a) mod 256 = int c" .
  
  from helper1 helper2 show ?thesis by simp
qed

end
