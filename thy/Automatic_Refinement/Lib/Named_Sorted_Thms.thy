section {* Named Theorems with Explicit Filtering and Sorting *}
theory Named_Sorted_Thms
imports Attr_Comb
begin
ML {*
  signature NAMED_SORTED_THMS =
  sig
    val member: Proof.context -> thm -> bool
    val get: Proof.context -> thm list
    val add_thm: thm -> Context.generic -> Context.generic
    val del_thm: thm -> Context.generic -> Context.generic
    val add: attribute
    val del: attribute
    val setup: theory -> theory
  end;

  functor Named_Sorted_Thms(
    val name: binding 
    val description: string
    val sort: Context.generic -> thm list -> thm list
    val transform: Context.generic -> thm -> thm list 
      (* Raise THM on invalid thm *)
    ): NAMED_SORTED_THMS =
  struct

    structure Data = Generic_Data
    (
      type T = thm Item_Net.T;
      val empty = Thm.full_rules;
      val extend = I;
      val merge = Item_Net.merge;
    );

    val member = Item_Net.member o Data.get o Context.Proof;

    fun content context = sort context (Item_Net.content (Data.get context));
    val get = content o Context.Proof;

    fun wrap upd = Thm.declaration_attribute (fn thm => fn context => let
      fun warn (msg,i,thms) = let
        val ctxt = Context.proof_of context
        val pt = Pretty.block [
          Pretty.str msg, 
          Pretty.brk 1,
          Pretty.block 
            [Pretty.str "(",Pretty.str (string_of_int i),Pretty.str ")"],
          Pretty.brk 1,
          Pretty.block (Pretty.fbreaks (map (Thm.pretty_thm ctxt) thms))
        ]
      in
        warning (Pretty.string_of pt)
      end

      val thms = (transform context thm) handle THM e => (warn e; [])
    in
      fold upd thms context
    end)

    val add = wrap (Data.map o Item_Net.update)
    val del = wrap (Data.map o Item_Net.remove)

    fun add_thm thm = Thm.apply_attribute (add) thm #> snd
    fun del_thm thm = Thm.apply_attribute (del) thm #> snd

    val setup =
      Attrib.setup name (Attrib.add_del add del) 
        ("declaration of " ^ description) 
      #> Global_Theory.add_thms_dynamic (name, content);

  end;

*}

end
