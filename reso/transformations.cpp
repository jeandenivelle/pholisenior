
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
   std::cout << pol << "\n";
   throw std::logic_error( "cannot negate" ); 
}

logic::selector reso::demorgan( logic::selector sel, polarity pol )
{
   if( pol == pol_pos || pol == pol_prop )
   {
      // We still check:

      switch( sel )
      {
      case logic::op_kleene_and:
      case logic::op_kleene_or:
      case logic::op_kleene_forall:
      case logic::op_kleene_exists:
         return sel;
      }

   }
   else
   {
      switch( sel )
      {
      case logic::op_kleene_and:
         return logic::op_kleene_or;
 
      case logic::op_kleene_or:
         return logic::op_kleene_and; 

      case logic::op_kleene_forall:
         return logic::op_kleene_exists;

      case logic::op_kleene_exists:
         return logic::op_kleene_forall;
      }
   }

   std::cout << "demorgan " << sel << " / " << pol << "\n";
   throw std::runtime_error( "De Morgan: unhandled case" ); 
}

logic::term 
reso::nnf( logic::beliefstate& blfs, namegenerator& gen,
           logic::context& ctxt, logic::term f, const polarity pol, 
           const unsigned int eq )
{
   if( true )
   {
      std::cout << ctxt << "\n";
      std::cout << pol << ":   " << f << "\n";
      std::cout << "eq = " << eq << "\n";
   }

   // We handle the prop-cases separately in the else: 

   if( pol == pol_pos || pol == pol_neg )
   {
      switch( f. sel( ))
      {

      case logic::op_implies:
      case logic::op_lazy_implies:
         {
            auto bin = f. view_binary( ); 

            auto sub1 = nnf( blfs, gen, ctxt, bin. sub1( ), negate( pol ), eq );
            auto sub2 = nnf( blfs, gen, ctxt, bin. sub2( ), pol, eq );

            return logic::term( demorgan( logic::op_kleene_or, pol ),
                                { sub1, sub2 } );
         }

      case logic::op_and:
      case logic::op_or:
      case logic::op_lazy_and:
         {
            auto bin = f. view_binary( );
            auto sub1 = nnf( blfs, gen, ctxt, bin. sub1( ), pol, eq );
            auto sub2 = nnf( blfs, gen, ctxt, bin. sub2( ), pol, eq );

            auto kleenop = f. sel( );
            if( f. sel( ) == logic::op_and )
               kleenop = logic::op_kleene_and;
            if( f. sel( ) == logic::op_or )
               kleenop = logic::op_kleene_or;
            if( f. sel( ) == logic::op_lazy_and )
               kleenop = logic::op_kleene_and;

            return logic::term( demorgan( kleenop, pol ), { sub1, sub2 } );   
         } 

      case logic::op_forall:
      case logic::op_kleene_forall:
      case logic::op_exists:
      case logic::op_kleene_exists:
         {
            auto q = f. view_quant( );

            size_t ss = ctxt. size( );
            for( size_t i = 0; i != q. size( ); ++ i )
               ctxt. extend( q. var(i). pref, q. var(i). tp );

            auto res = nnf( blfs, gen, ctxt, q. body( ), pol, eq );

            logic::selector kleenequant = f. sel( );

            if( kleenequant == logic::op_forall )
               kleenequant = logic::op_kleene_forall;

            if( kleenequant == logic::op_exists )
               kleenequant = logic::op_kleene_exists;

            // Now we are a real Kleene quantifier. 

            res = logic::term( demorgan( kleenequant, pol ), res, 
                               std::initializer_list< logic::vartype > ( ));

            // Add the quantified variables/types from the original formula:

            for( size_t i = 0; i != q. size( ); ++ i )
               res. view_quant( ). push_back( q. var(i));

            ctxt. restore( ss ); 
            return res; 
         } 

      case logic::op_equals:
      case logic::op_apply:
         if( pol == pol_pos )
            return f;
         if( pol == pol_neg )
            return logic::term( logic::op_not, f ); 

         throw std::logic_error( "should never been here" );
      }
      std::cout << "reso::nnf " << f. sel( ) << "\n";
      throw std::runtime_error( "unhandled selector" ); 
   }
   else
   {
      // Cases for # or !# : 
 
      switch( f. sel( ))
      {

      case logic::op_and:
      case logic::op_or:
      case logic::op_implies:
      case logic::op_equiv:
         {
            auto eager = f. view_binary( ); 

            auto sub1 = nnf( blfs, gen, ctxt, eager. sub1( ), pol, eq );
            auto sub2 = nnf( blfs, gen, ctxt, eager. sub2( ), pol, eq );
            return logic::term( demorgan( logic::op_kleene_and, pol ),
                                { sub1, sub2 } );
         }

      case logic::op_lazy_and:
      case logic::op_lazy_or:
      case logic::op_lazy_implies:
         {
            auto lazy = f. view_binary( ); 
            auto sub1prop = nnf( blfs, gen, ctxt, lazy. sub1( ), pol, eq );
            std::cout << sub1prop << "\n"; 
           
            polarity sub1pol = ( f. sel( ) == logic::op_lazy_and || 
                                 f. sel( ) == logic::op_lazy_implies ) ? 
                           pol_neg : pol_pos;

            if( pol == pol_negprop )
               sub1pol = negate( sub1pol );

            std::cout << sub1pol << "\n";
            auto sub1 = nnf( blfs, gen, ctxt, lazy.sub1( ), sub1pol, eq );
            std::cout << sub1 << "\n";

            auto sub2prop = nnf( blfs, gen, ctxt, lazy. sub2( ), pol, eq );
            std::cout << sub2prop << "\n";

            return logic::term( demorgan( logic::op_kleene_and, pol ),
                { sub1prop, logic::term( demorgan( logic::op_kleene_or, pol ), 
                     { sub1, sub2prop } ) } ); 
         }

      case logic::op_forall:
      case logic::op_exists:
         {
            auto q = f. view_quant( );

            size_t ss = ctxt. size( );
            for( size_t i = 0; i != q. size( ); ++ i )
               ctxt. extend( q. var(i). pref, q. var(i). tp );

            auto res = nnf( blfs, gen, ctxt, q. body( ), pol, eq );

            res = logic::term( demorgan( logic::op_kleene_forall, pol ), 
                               res,
                               std::initializer_list< logic::vartype > ( ));

            // Add the quantified variables/types from the original formula:

            for( size_t i = 0; i != q. size( ); ++ i )
               res. view_quant( ). push_back( q. var(i));

            ctxt. restore( ss );

            return res; 
         }

      case logic::op_apply:
         if( pol == pol_prop )
            return logic::term( logic::op_prop, f );

         if( pol == pol_negprop )
         {
            return logic::term( logic::op_not,
                      logic::term( logic::op_prop, f ));
         }

         throw std::logic_error( "should not have been here" );
      }
      std::cout << pol << " : " << f. sel( ) << "\n";
      throw std::runtime_error( "prop not handled" );
   }
}




