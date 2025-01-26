
#ifndef RESO_TRANSFORMATIONS_
#define RESO_TRANSFORMATIONS_

#include "logic/term.h"
#include "logic/beliefstate.h"
#include "logic/context.h"

#include "namegenerators.h"
#include "polarity.h"

namespace reso
{


   logic::term atom( identifier pred, const logic::type& predtype );
   logic::term forall( const logic::type& predtype, logic::term form );

   logic::term
   define_subform( logic::beliefstate& blfs, namegenerators& gen,
                   logic::context& ctxt, logic::term t, 
                   logic::selector defop );
      // defop is the operator that will be used in the definition.
      // It can be op_equiv, op_implies, or op_kleene_or.
 
   logic::term
   clausify( logic::beliefstate& blfs, namegenerators& gen,
             logic::context& ctxt, logic::term& f, unsigned int alt );
      // Term f must have Kleene operations only, and in NNF.
      // Even level means and/forall.
      // Odd level means or/exists.

}

#endif

