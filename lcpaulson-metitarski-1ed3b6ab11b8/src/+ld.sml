(*Detect Poly versus SML/NJ*)
val poly = String.isSubstring "poly" (CommandLine.name());

PolyML.Compiler.reportUnreferencedIds := true;

use "Portable.sig";
use"Random.sig"; use"Random.sml";
if poly then use "PortablePolyml.sml"
        else use "PortableSmlNJ.sml";
use"Polyhash.sig"; use"Polyhash.sml";
use"Useful.sig"; use"Useful.sml";
use"rat.sml";  (*John Harrison's code*)
use"Lazy.sig"; use"Lazy.sml";
use"Map.sig"; use"Map.sml";
use"Set.sig"; use"Set.sml";
use"Ordered.sig"; use"Ordered.sml";
use"KeyMap.sig"; use"KeyMap.sml";
use"ElementSet.sig"; use"ElementSet.sml";
use"Sharing.sig"; use"Sharing.sml";
use"Stream.sig"; use"Stream.sml";
use"Heap.sig"; use"Heap.sml";
use"Print.sig"; use"Print.sml";
use"Parse.sig"; use"Parse.sml";
use"Name.sig"; use"Name.sml";
use"NameArity.sig"; use"NameArity.sml";
use"Term.sig"; use"Term.sml";
use"Subst.sig"; use"Subst.sml";
use"Atom.sig"; use"Atom.sml";
use"Formula.sig"; use"Formula.sml";
use"Literal.sig"; use"Literal.sml";
use"KnuthBendixOrder.sig"; use"KnuthBendixOrder.sml";
use"Poly.sig"; use"Poly.sml";
use"RCF/Common.sig"; use"RCF/Common.sml";
use"RCF/Algebra.sig"; use"RCF/Algebra.sml";
use"RCF/Groebner.sig"; use"RCF/Groebner.sml";
use"RCF/SMT.sig"; use"RCF/SMT.sml";
use"RCF/IntvlsFP.sig"; use"RCF/IntvlsFP.sml";
use"RCF/Resultant.sig"; use"RCF/Resultant.sml";
use"RCF/Sturm.sig"; use"RCF/Sturm.sml";
use"RCF/RealAlg.sig"; use"RCF/RealAlg.sml";
use"RCF/MTAlgebra.sig"; use"RCF/MTAlgebra.sml";
use"RCF/CADProjO.sig"; use"RCF/CADProjO.sml";
use"RCF/Mathematica.sig"; use"RCF/Mathematica.sml";
use"RCF/Qepcad.sig"; use"RCF/Qepcad.sml";
use"RCF/Nullsatz.sig"; use"RCF/Nullsatz.sml";
use"RCF/CertRCFk.sig"; use"RCF/CertRCFk.sml";
use"RCF/CertRCFp.sig"; use"RCF/CertRCFp.sml";
use"RCF/RCF.sig"; use"RCF/RCF.sml";
use"Thm.sig"; use"Thm.sml";
use"Proof.sig"; use"Proof.sml";
use"Rule.sig"; use"Rule.sml";
use"Normalize.sig"; use"Normalize.sml";
use"Model.sig"; use"Model.sml";
use"Problem.sig"; use"Problem.sml";
use"TermNet.sig"; use"TermNet.sml";
use"AtomNet.sig"; use"AtomNet.sml";
use"LiteralNet.sig"; use"LiteralNet.sml";
use"Subsume.sig"; use"Subsume.sml";
use"Rewrite.sig"; use"Rewrite.sml";
use"Units.sig"; use"Units.sml";
use"Clause.sig"; use"Clause.sml";
use"Active.sig"; use"Active.sml";
use"Waiting.sig"; use"Waiting.sml";
use"SplitStack.sig"; use"SplitStack.sml";
use"Resolution.sig"; use"Resolution.sml";
use"Tptp.sig"; use"Tptp.sml";
use"SMTLIB.sig"; use"SMTLIB.sml";

use"Syntax/load.sml";

use"Options.sig"; use"Options.sml";
use"metis.sml";
