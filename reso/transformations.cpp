
#include "transformations.h"

const char* reso::getcstring( polarity pol )
{
   switch( pol )
   {
   case pol_pos:       return "pos"; 
   case pol_neg:       return "neg";
   case pol_prop:      return "prop";
   case pol_negprop:   return "neg-prop";
   default:            return "???";
   }
}

reso::polarity reso::negate( reso::polarity pol )
{
   switch( pol )
   {
   case pol_pos:       return pol_neg;
   case pol_neg:       return pol_pos;
   case pol_prop:      return pol_negprop;
   case pol_negprop:   return pol_prop;
   }
   throw std::runtime_error( "cannot negate" ); 
}

logic::term 
reso::nnf( logic::beliefstate& blfs, logic::context& ctxt, 
           logic::term f, polarity pol, unsigned int equivs )
{
   std::cout << ctxt << "\n";
   std::cout << pol << " :   " << f << "\n";
   std::cout << "equivs = " << equivs << "\n";

   // We handle the prop-cases separately:

   if( pol == pol_pos || pol == pol_neg )
   {
      switch( f. sel( ))
      {

      case logic::op_implies:
      case logic::op_lazy_implies:
         {
            auto bin = f. view_binary( ); 

            auto sub1 = nnf( blfs, ctxt, bin. sub1( ), negate( pol ), equivs );
            auto sub2 = nnf( blfs, ctxt, bin. sub2( ), pol, equivs );

            std::cout << "sub1 = " << sub1 << "\n";
            std::cout << "sub2 = " << sub2 << "\n";

            throw std::runtime_error( "unfinished" ); 
         }
 
      case logic::op_forall:
      case logic::op_kleene_forall:
         {
            auto q = f. view_quant( );

            size_t ss = ctxt. size( );
            for( size_t i = 0; i != q. size( ); ++ i )
            {
               ctxt. extend( q. var(i). pref, q. var(i). tp );
            }

            auto bod = nnf( blfs, ctxt, q. body( ), pol, equivs );

            throw std::runtime_error( "quant, rest not implemented" );
         } 




      }
      std::cout << "reso::nnf " << f. sel( ) << "\n";
      throw std::runtime_error( "unhandled selector" ); 
   }
   else
   {



      throw std::runtime_error( "prop not handled" );
   }
}




