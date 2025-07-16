
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

   case prf_ident:
      {
         auto id = prf. view_ident( ). ident( );
         const auto& f = seq. blfs. getformulas( id ); 
         if( f. empty( ))
            throw std::logic_error( "not found" );
         if( f. size( ) > 1 )
            throw std::logic_error( "too many" ); 

         return seq. getformula( f. front( ));
      }
   }

   std::cout << prf. sel( ) << "\n";
   throw std::logic_error( "dont know how to check proof term" );
}



