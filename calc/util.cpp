
#include "util.h"

bool calc::isatom( const logic::term& f )
{
   switch( f. sel( ))
   {
   case logic::op_exact:
   case logic::op_debruijn:
   case logic::op_unchecked:
   case logic::op_equals:
   case logic::op_apply:
      return true;
   default:
      return false;
   }
}

bool calc::isliteral( const logic::term& f )
{
   if( f. sel( ) == logic::op_not || f. sel( ) == logic::op_prop )
      return isliteral( f. view_unary( ). sub( ));
   else
      return isatom(f);
}


logic::term
calc::quantify( logic::selector op, const logic::context& ctxt,
                const logic::term& body )
{
   if( ctxt. size( ) == 0 )
      return body;
   else
   {
      auto res = logic::term( op, body,
                              std::initializer_list< logic::vartype > ( ));
      auto q = res. view_quant( );

      // We need to do in reverse order, because context looks back:

      for( size_t i = ctxt. size( ); i -- ; )
         q. push_back( logic::vartype( ctxt. getname(i), ctxt. gettype(i) ));
      return res;
   }
}


