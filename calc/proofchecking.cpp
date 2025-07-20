
#include "proofchecking.h"

#include "removelets.h"
#include "alternating.h"

#include "logic/pretty.h"

logic::term 
calc::eval( const proofterm& prf, sequent& seq, errorstack& err )
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

   case prf_clausify:
      {
         auto cl = prf. view_clausify( ); 
         auto fm = eval( cl. parent( ), seq, err );
         logic::context ctxt;  
         fm = removelets( seq, ctxt, fm );
         if( ctxt. size( ))
            throw std::logic_error( "context not empty" ); 

         fm = alternating( fm, logic::op_kleene_and, 2 );
         return fm;    
      }
   }

   std::cout << prf. sel( ) << "\n";
   throw std::logic_error( "dont know how to check proof term" );
}



