
#ifndef RESO_TRANSFORMATIONS_
#define RESO_TRANSFORMATIONS_

#include "logic/term.h"
#include "logic/beliefstate.h"
#include "logic/context.h"

#include "namegenerators.h"
#include "polarity.h"

namespace reso
{

   bool issimple( const logic::term& f );
      // True if f is simple. Currently this means:
      // Does not contain any binary operators.

   logic::term
   repl_equiv( logic::beliefstate& blfs, namegenerators& gen,
               logic::context& ctxt, logic::term f, unsigned int equivs );

      // Replace nested equivalences by definitions.

   logic::term nnf( logic::term f, polarity pol );
   logic::term nnf_prop( logic::term f, polarity pol );

   logic::term flatten( logic::term f );
      // The formula must be in NNF, which implies that it contains
      // only Kleene operators.
      // Factor forall x P(X) & Q(X) --> forall X P(X) & forall X Q(X)
      //        exists x P(X) | Q(x) --> exists X P(X) | exists X Q(X).
      //        Merge nested | and & 
      //        Merge nested forall and exist.
 
   // Create a definition for the formula:

   logic::term
   repl_subform( logic::beliefstate& blfs, namegenerators& gen,
                 logic::context& ctxt, logic::term t, bool equiv );

   logic::term
   clausify( logic::beliefstate& blfs, namegenerators& gen,
             logic::context& ctxt, logic::term& f, unsigned int alt );
      // Term f must have Kleene operations only, and in NNF.
      // Even level means and/forall.
      // Odd level means or/exists.

}

#endif

