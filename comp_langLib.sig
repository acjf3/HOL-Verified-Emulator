signature comp_langLib =
sig

    include Abbrev

    val define_compiler_exp   : string -> term -> thm

end
