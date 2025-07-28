
#ifndef CALC_UNIFY_
#define CALC_UNIFY_

#include "apart.h"
#include "indexedstack.h"

namespace calc
{
   using unifsubst = 
   indexedstack< apart<size_t>, apart< const logic::term* >, 
                 apart<size_t> :: hash, apart<size_t> :: equal_to > ; 

   bool 
   unify( unifsubst& subst, 
          apart< const logic::term* > t1, size_t exists1, size_t vardepth1,
          apart< const logic::term* > t2, size_t exists2, size_t vardepth2 );
      // Existential variables (DeBruijn indices) are treated like constants.
}

#endif

