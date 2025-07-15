
#include "proofchecking.h"

logic::term 
calc::eval( sequent& seq, const proofterm& prf, errorstack& err )
{
   std::cout << "evaluating " << prf << "\n";

   switch( prf. sel( ))
   {
   case prf_truthconst:
      return logic::term( logic::op_kleene_and,
                             std::initializer_list< logic::term > ( ));
   case prf_exact:
      {
         auto ex = prf. view_exact( ). exact( );
         return seq. getformula( ex ); 
      }

   }

   std::cout << prf. sel( ) << "\n";
   throw std::logic_error( "dont know how to check proof term" );
}



