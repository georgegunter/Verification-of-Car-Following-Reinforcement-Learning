AUTOMAKE_OPTIONS=foreign

bin_PROGRAMS = metit

metit_SOURCES = src/Portable.sig  src/PortablePolyml.sml  src/PortableSmlNJ.sml  \
       src/Random.sig src/Random.sml    \
       src/rat.sml                      \
       src/Useful.sig src/Useful.sml    \
       src/Polyhash.sig src/Polyhash.sml        \
       src/Lazy.sig src/Lazy.sml        \
       src/Set.sig src/Set.sml  \
       src/Ordered.sig src/Ordered.sml  \
       src/ElementSet.sig src/ElementSet.sml    \
       src/Map.sig src/Map.sml  \
       src/KeyMap.sig src/KeyMap.sml    \
       src/Sharing.sig src/Sharing.sml  \
       src/Stream.sig src/Stream.sml    \
       src/Heap.sig src/Heap.sml        \
       src/Print.sig src/Print.sml \
       src/Parse.sig src/Parse.sml \
       src/Options.sig src/Options.sml  \
       src/Name.sig src/Name.sml        \
       src/NameArity.sig src/NameArity.sml \
       src/Term.sig src/Term.sml        \
       src/Subst.sig src/Subst.sml      \
       src/Atom.sig src/Atom.sml        \
       src/Formula.sig src/Formula.sml  \
       src/Literal.sig src/Literal.sml  \
       src/Thm.sig src/Thm.sml  \
       src/Proof.sig src/Proof.sml      \
       src/Rule.sig src/Rule.sml        \
       src/Normalize.sig src/Normalize.sml      \
       src/Model.sig src/Model.sml      \
       src/Problem.sig src/Problem.sml  \
       src/Poly.sig  src/Poly.sml       \
       src/TermNet.sig src/TermNet.sml  \
       src/AtomNet.sig src/AtomNet.sml  \
       src/LiteralNet.sig src/LiteralNet.sml    \
       src/Subsume.sig src/Subsume.sml  \
       src/KnuthBendixOrder.sig src/KnuthBendixOrder.sml        \
       src/Rewrite.sig src/Rewrite.sml  \
       src/Units.sig src/Units.sml      \
       src/Clause.sig src/Clause.sml    \
       src/Active.sig src/Active.sml    \
       src/Waiting.sig src/Waiting.sml  \
       src/RCF/Common.sig src/RCF/Common.sml   \
       src/RCF/Algebra.sig src/RCF/Algebra.sml  \
       src/RCF/Groebner.sig src/RCF/Groebner.sml \
       src/RCF/SMT.sig src/RCF/SMT.sml  \
       src/RCF/IntvlsFP.sig src/RCF/IntvlsFP.sml  \
       src/RCF/Resultant.sig src/RCF/Resultant.sml \
       src/RCF/Sturm.sig src/RCF/Sturm.sml   \
       src/RCF/RealAlg.sig src/RCF/RealAlg.sml  \
       src/RCF/MTAlgebra.sig src/RCF/MTAlgebra.sml  \
       src/RCF/CADProjO.sig src/RCF/CADProjO.sml \
       src/RCF/Mathematica.sig src/RCF/Mathematica.sml  \
       src/RCF/Qepcad.sig src/RCF/Qepcad.sml  \
       src/RCF/Nullsatz.sig src/RCF/Nullsatz.sml   \
       src/RCF/CertRCFk.sig src/RCF/CertRCFk.sml  \
       src/RCF/CertRCFp.sig src/RCF/CertRCFp.sml  \
       src/RCF/RCF.sig src/RCF/RCF.sml  \
       src/SplitStack.sig src/SplitStack.sml \
       src/Resolution.sig src/Resolution.sml    \
       src/SMTLIB.sig src/SMTLIB.sml  \
       src/Syntax/load.sml  \
       src/Tptp.sig src/Tptp.sml        \
       src/metis.sml src/+ld.sml

metit_LDADD = metit.o

CD = OS.FileSys.chDir

metit.o: $(metit_SOURCES)
	echo '$(CD)"src"; use"+ld.sml"; $(CD)".."; PolyML.export("metit",metis);' | $(POLY)

install-exec-local: 
	echo '"metit installed in "$(bindir)'
