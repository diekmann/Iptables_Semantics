(*  Title:      Uint_Userguide.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter {* User guide for native words *}

(*<*)
theory Uint_Userguide imports
  Uint32
  Uint16
  Code_Target_Bits_Int
begin
(*>*)

text {*
  This tutorial explains how to best use the types for native
  words like @{typ "uint32"} in your formalisation.
  You can base your formalisation
  \begin{enumerate}
  \item either directly on these types,
  \item or on the generic @{typ "'a word"} and only introduce native
    words a posteriori via code generator refinement.
  \end{enumerate}

  The first option causes the least overhead if you have to prove only
  little about the words you use and start a fresh formalisation.
  Just use the native type @{typ uint32} instead of @{typ "32 word"}
  and similarly for @{text uint16} and @{text uint8}.
  As native word types are meant only for code generation, the lemmas
  about @{typ "'a word"}  have not been duplicated, but you can transfer
  theorems between native word types and @{typ "'a word"} using the
  transfer package.

  Note, however, that this option restricts your work a bit:
  your own functions cannot be ``polymorphic'' in the word length,
  but you have to define a separate function for every word length you need.

  The second option is recommended if you already have a formalisation
  based on @{typ "'a word"} or if your proofs involve words and their
  properties. It separates code generation from modelling and proving,
  i.e., you can work with words as usual. Consequently, you have to
  manually setup the code generator to use the native types wherever
  you want. The following describes how to achieve this with moderate
  effort.

  Note, however, that some target languages of the code generator
  (especially OCaml) do not support all the native word types provided.
  Therefore, you should only import those types that you need -- the
  theory file for each type mentions at the top the restrictions for
  code generation. For example, PolyML does not provide the Word16
  structure, and OCaml provides neither Word8 nor Word16.
  You can still use these theories provided that you also import
  the theory @{theory "Code_Target_Bits_Int"} (which implements
  @{typ int} by target-language integers), but these words will
  be implemented via Isabelle's @{text "HOL-Word"} library, i.e.,
  you do not gain anything in terms of efficiency.

  \textbf{There is a separate code target @{text "SML_word"} for SML.}
  If you use one of the native words that PolyML does not support
  (such as @{text "uint16"}), but would like to map its operations
  to the Standard Basis Library functions, make sure to use the target
  @{text "SML_word"} instead of @{text "SML"};  if you only use native
  word sizes that PolyML supports, you can stick with @{text "SML"}.
  This ensures that code generation within Isabelle as used by 
  @{text Quickcheck}, @{text value} and @\{code\} in ML blocks
  continues to work.
*}

section {* Lifting functions from @{typ "'a word"} to native words *}

text {*
  This section shows how to convert functions from @{typ "'a word"} to native 
  words. For example, the following function @{text sum_squares} computes 
  the sum of the first @{term n} square numbers in 16 bit arithmetic using
  a tail-recursive function @{text gen_sum_squares} with accumulator;
  for convenience, @{text sum_squares_int} takes an integer instead of a word.
*}

function gen_sum_squares :: "16 word \<Rightarrow> 16 word \<Rightarrow> 16 word" where (*<*)[simp del]:(*>*)

  "gen_sum_squares accum n =
   (if n = 0 then accum else gen_sum_squares (accum + n * n) (n - 1))"
(*<*)by pat_completeness simp
termination by(relation "measure (nat \<circ> uint \<circ> snd)")
  (simp_all, metis (hide_lams, mono_tags) uint_1 uint_eq_0 uint_minus_simple_alt uint_sub_ge word_le_sub1 word_less_def word_neq_0_conv word_zero_le zle_diff1_eq)(*>*)


definition sum_squares :: "16 word \<Rightarrow> 16 word" where
   "sum_squares = gen_sum_squares 0"

definition sum_squares_int :: "int \<Rightarrow> 16 word" where
  "sum_squares_int n = sum_squares (word_of_int n)"

text {*
  The generated code for @{term sum_squares} and @{term sum_squares_int} 
  emulates words with unbounded integers and explicit modulus as specified 
  in the theory @{theory Word}. But for efficiency, we want that the
  generated code uses machine words and machine arithmetic. Unfortunately,
  as @{typ "'a word"} is polymorphic in the word length, the code generator
  can only do this if we use another type for machine words. The theory
  @{theory Uint16} defines the type @{typ uint16} for machine words of
  16~bits. We just have to follow two steps to use it:
  
  First, we lift all our functions from @{typ "16 word"} to @{typ uint16},
  i.e., @{term sum_squares}, @{term gen_sum_squares}, and 
  @{term sum_squares_int} in our case. The theory @{theory Uint16} sets
  up the lifting package for this and has already taken care of the
  arithmetic and bit-wise operations.
*}
lift_definition gen_sum_squares_uint :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" 
  is gen_sum_squares .
lift_definition sum_squares_uint :: "uint16 \<Rightarrow> uint16" is sum_squares .
lift_definition sum_squares_int_uint :: "int \<Rightarrow> uint16" is sum_squares_int .

text {*
  Second, we also have to transfer the code equations for our functions.
  The attribute @{text Transfer.transferred} takes care of that, but it is
  better to check that the transfer succeeded: inspect the theorem to check
  that the new constants are used throughout.
*}

lemmas [Transfer.transferred, code] =
  gen_sum_squares.simps
  sum_squares_def
  sum_squares_int_def

text {*
  Finally, we export the code to standard ML.  We use the target
  @{text "SML_word"} instead of @{text "SML"} to have the operations
  on @{typ uint16} mapped to the Standard Basis Library. As PolyML
  does not provide a Word16 type, the mapping for @{typ uint16} is only
  active in the refined target @{text "SML_word"}.
*}
export_code sum_squares_int_uint in SML_word

text {*
  Nevertheless, we can still evaluate terms with @{term "uint16"} within 
  Isabelle, i.e., PolyML, but this will be translated to @{typ "16 word"}
  and therefore less efficient.
*}

value "sum_squares_int_uint 40"

section {* Storing native words in datatypes *}

text {*
  The above lifting is necessary for all functions whose type mentions
  the word type. Fortunately, we do not have to duplicate functions that
  merely operate on datatypes that contain words. Nevertheless, we have
  to tell the code generator that these functions should call the new ones,
  which operate on machine words. This section shows how to achieve this
  with data refinement.
*}

subsection {* Example: expressions and two semantics *}

text {*
  As the running example, we consider a language of expressions (literal values, less-than comparisions and conditional) where values are either booleans or 32-bit words.
  The original specification uses the type @{typ "32 word"}.
*}

datatype val = Bool bool | Word "32 word"
datatype expr = Lit val | LT expr expr | IF expr expr expr

abbreviation (input) word :: "32 word \<Rightarrow> expr" where "word i \<equiv> Lit (Word i)"
abbreviation (input) bool :: "bool \<Rightarrow> expr" where "bool i \<equiv> Lit (Bool i)"

-- {* Denotational semantics of expressions, @{term None} denotes a type error *}
fun eval :: "expr \<Rightarrow> val option" where
  "eval (Lit v) = Some v"
| "eval (LT e\<^sub>1 e\<^sub>2) = 
  (case (eval e\<^sub>1, eval e\<^sub>2) 
   of (Some (Word i\<^sub>1), Some (Word i\<^sub>2)) \<Rightarrow> Some (Bool (i\<^sub>1 < i\<^sub>2))
   | _ \<Rightarrow> None)"
| "eval (IF e\<^sub>1 e\<^sub>2 e\<^sub>3) =
  (case eval e\<^sub>1 of Some (Bool b) \<Rightarrow> if b then eval e\<^sub>2 else eval e\<^sub>3
   | _ \<Rightarrow> None)"

-- {* Small-step semantics of expressions, it gets stuck upon type errors. *}
inductive step :: "expr \<Rightarrow> expr \<Rightarrow> bool" ("_ \<rightarrow> _" [50, 50] 60) where
  "e \<rightarrow> e' \<Longrightarrow> LT e e\<^sub>2 \<rightarrow> LT e' e\<^sub>2"
| "e \<rightarrow> e' \<Longrightarrow> LT (word i) e \<rightarrow> LT (word i) e'"
| "LT (word i\<^sub>1) (word i\<^sub>2) \<rightarrow> bool (i\<^sub>1 < i\<^sub>2)"
| "e \<rightarrow> e' \<Longrightarrow> IF e e\<^sub>1 e\<^sub>2 \<rightarrow> IF e' e\<^sub>1 e\<^sub>2"
| "IF (bool True) e\<^sub>1 e\<^sub>2 \<rightarrow> e\<^sub>1"
| "IF (bool False) e\<^sub>1 e\<^sub>2 \<rightarrow> e\<^sub>2"

-- {* Compile the inductive definition with the predicate compiler *}
code_pred (modes: i \<Rightarrow> o \<Rightarrow> bool as reduce, i \<Rightarrow> i \<Rightarrow> bool as step') step .

subsection {* Change the datatype to use machine words *}

text {* 
  Now, we want to use @{typ uint32} instead of @{typ "32 word"}.
  The goal is to make the code generator use the new type without
  duplicating any of the types (@{typ val}, @{typ expr}) or the
  functions (@{term eval}, @{term reduce}) on such types.

  The constructor @{term Word} has @{typ "32 word"} in its type, so
  we have to lift it to @{text "Word'"}, and the same holds for the
  case combinator @{term case_val}, which @{term case_val'} replaces.%
  \footnote{%
    Note that we should not declare a case translation for the new
    case combinator because this will break parsing case expressions
    with old case combinator.
  }
  Next, we set up the code generator accordingly:
  @{term Bool} and @{term Word'} are the new constructors for @{typ val},
  and @{term case_val'} is the new case combinator with an appropriate 
  case certificate.%
  \footnote{%
    Case certificates tell the code generator to replace the HOL
    case combinator for a datatype with the case combinator of the
    target language.  Without a case certificate, the code generator
    generates a function that re-implements the case combinator; 
    in a strict languages like ML or Scala, this means that the code
    evaluates all possible cases before it decides which one is taken.

    Case certificates are described in Haftmann's PhD thesis
    \cite[Def.\ 27]{Haftmann2009PhD}. For a datatype @{text dt}
    with constructors @{text "C\<^sub>1"} to @{text "C\<^sub>n"}
    where each constructor @{text "C\<^sub>i"} takes @{text "k\<^sub>i"} parameters,
    the certificate for the case combinator @{text "case_dt"}
    looks as follows:

    {
      \isamarkuptrue\isacommand{lemma}\isamarkupfalse\isanewline%
      \ \ \isakeyword{assumes}\ {\isachardoublequoteopen}CASE\ {\isasymequiv}\ dt{\isacharunderscore}case\ c\isactrlsub {\isadigit{1}}\ c\isactrlsub {\isadigit{2}}\ \ldots\ c\isactrlsub{n}{\isachardoublequoteclose}\isanewline
      \ \ \isakeyword{shows}\ {\isachardoublequoteopen}{\isacharparenleft}CASE\ {\isacharparenleft}C\isactrlsub {\isadigit{1}}\ a\isactrlsub {\isadigit{1}}\isactrlsub {\isadigit{1}}\ a\isactrlsub {\isadigit{1}}\isactrlsub {\isadigit{2}}\ \ldots\ a\isactrlsub {\isadigit{1}}\isactrlsub {k\ensuremath{{}_1}}{\isacharparenright}\ {\isasymequiv}\ c\isactrlsub {\isadigit{1}}\ a\isactrlsub {\isadigit{1}}\isactrlsub {\isadigit{1}}\ a\isactrlsub {\isadigit{1}}\isactrlsub {\isadigit{2}}\ \ldots\ a\isactrlsub {\isadigit{1}}\isactrlsub {k\ensuremath{{}_1}}{\isacharparenright}\isanewline
      \ \ \ \ {\isacharampersand}{\isacharampersand}{\isacharampersand}\ {\isacharparenleft}CASE\ {\isacharparenleft}C\isactrlsub {\isadigit{2}}\ a\isactrlsub {\isadigit{2}}\isactrlsub {\isadigit{1}}\ a\isactrlsub {\isadigit{2}}\isactrlsub {\isadigit{2}}\ \ldots\ a\isactrlsub {\isadigit{2}}\isactrlsub {k\ensuremath{{}_2}}{\isacharparenright}\ {\isasymequiv}\ c\isactrlsub {\isadigit{2}}\ a\isactrlsub {\isadigit{2}}\isactrlsub {\isadigit{1}}\ a\isactrlsub {\isadigit{2}}\isactrlsub {\isadigit{2}}\ \ldots\ a\isactrlsub {\isadigit{2}}\isactrlsub {k\ensuremath{{}_2}}{\isacharparenright}\isanewline
      \ \ \ \ {\isacharampersand}{\isacharampersand}{\isacharampersand}\ \ldots\isanewline
      \ \ \ \ {\isacharampersand}{\isacharampersand}{\isacharampersand}\ {\isacharparenleft}CASE\ {\isacharparenleft}C\isactrlsub {n}\ a\isactrlsub {n}\isactrlsub {\isadigit{1}}\ a\isactrlsub {n}\isactrlsub {\isadigit{2}}\ \ldots\ a\isactrlsub {n}\isactrlsub {k\ensuremath{{}_n}}{\isacharparenright}\ {\isasymequiv}\ c\isactrlsub {n}\ a\isactrlsub {n}\isactrlsub {\isadigit{1}}\ a\isactrlsub {n}\isactrlsub {\isadigit{2}}\ \ldots\ a\isactrlsub {n}\isactrlsub {k\ensuremath{{}_n}}{\isacharparenright}{\isachardoublequoteclose}\isanewline
    }
  }
  We delete the code equations for the old constructor @{term Word}
  and case combinator @{term case_val} such that the code generator
  reports missing adaptations.
*}

lift_definition Word' :: "uint32 \<Rightarrow> val" is Word .

code_datatype Bool Word'

lift_definition case_val' :: "(bool \<Rightarrow> 'a) \<Rightarrow> (uint32 \<Rightarrow> 'a) \<Rightarrow> val \<Rightarrow> 'a" is case_val .

lemmas [code, simp] = val.case [Transfer.transferred]

lemma case_val'_cert:
  fixes bool word' b w
  assumes "CASE \<equiv> case_val' bool word'"
  shows "(CASE (Bool b) \<equiv> bool b) &&& (CASE (Word' w) \<equiv> word' w)"
by(simp_all add: assms)
setup {* Code.add_case @{thm case_val'_cert} *}

lemma [code, code del]: "case_val = case_val" ..
lemma [code, code del]: "Word = Word" ..

subsection {* Make functions use functions on machine words *}

text {*
  Finally, we merely have to change the code equations to use the 
  new functions that operate on @{typ uint32}. As before, the
  attribute @{text Transfer.transferred} does the job. In our example,
  we adapt the equality test on @{typ val} (code equations
  @{thm [source] val.eq.simps}) and the denotational and small-step 
  semantics (code equations @{thm [source] eval.simps} and
  @{thm [source] step.equation}, respectively).

  We check that the adaptation has suceeded by exporting the functions.
  As we only use native word sizes that PolyML supports, we can use 
  the usual target @{text "SML"} instead of @{text "SML_word"}.
*}

lemmas [code] = 
  val.eq.simps[THEN meta_eq_to_obj_eq, Transfer.transferred, THEN eq_reflection]
  eval.simps[Transfer.transferred]
  step.equation[Transfer.transferred]

export_code reduce step' eval in SML

section {* Troubleshooting *}

text {*
  This section explains some possible problems when using native words.
  If you experience other difficulties, please contact the author.
*}

subsection {* @{text export_code} raises an exception \label{section:export_code:exception} *}

text {*
  Probably, you have defined and are using a function on a native word type,
  but the code equation refers to emulated words. For example, the following
  defines a function @{text double} that doubles a word. When we try to export
  code for @{text double} without any further setup, @{text export_code} will
  raise an exception or generate code that does not compile.
*}

lift_definition double :: "uint32 \<Rightarrow> uint32" is "\<lambda>x. x + x" .

text {*
  We have to prove a code equation that only uses the existing operations on
  @{typ uint32}. Then, @{text export_code} works again.
*}

lemma double_code [code]: "double n = n + n"
by transfer simp

subsection {* The generated code does not compile *}

text {*
  Probably, you have been exporting to a target language for which there
  is no setup, or your compiler does not provide the required API. Every
  theory for native words mentions at the start the limitations on code
  generation. Check that your concrete application meets all the
  requirements.

  Alternatively, this might be an instance of the problem described 
  in \S\ref{section:export_code:exception}.

  For Haskell, you have to enable the extension TypeSynonymInstances with \texttt{-XTypeSynonymInstances}
  if you are using polymorphic bit operations on the native word types.
*}

subsection {* The generated code is too slow *}

text {*
  The generated code will most likely not be as fast as a direct implementation in the target language with manual tuning.
  This is because we want the configuration of the code generation to be sound (as it can be used to prove theorems in Isabelle).
  Therefore, the bit operations sometimes perform range checks before they call the target language API.
  Here are some examples:
  \begin{itemize}
  \item Shift distances and bit indices in target languages are often expected to fit into a bounded integer or word.
    However, the size of these types varies across target languages and platforms.
    Hence, no Isabelle/HOL type can model uniformly all of them.
    Instead, the bit operations use arbitrary-precision integers for such quantities and check at run-time that the values fit into a bounded integer or word, respectively -- if not, they raise an exception.
  
  \item Division and modulo operations explicitly test whether the divisor is $0$ and return the HOL value of division by $0$ in that case.
    This is necessary because some languages leave the behaviour of division by 0 unspecified.
  \end{itemize}
  
  If you have better ideas how to eliminate such checks and speed up the generated code without sacrificing soundness, please contact the author!
*}

(*<*)end(*>*)
