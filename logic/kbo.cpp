
#include "kbo.h"

logic::kbo::weight_t logic::kbo::weight( const type& tp )
{
#if 0
   switch( tp. sel( )) 
   {
   case type_form:
   case type_obj:
      return 1;
   case type_ident:
      return 1; 
   case type_func:
      {
         auto f = tp. view_func( ); 
         size_t w = weight( f. result( ));
         for( size_t i = 0; i != f. size( ); ++ i )
            w += weight( f. arg(i));
         return w; 
      }
   default:
      std::cerr << "the selector is " << tp. sel( ) << "\n";
      throw std::runtime_error( "wrong selector in type" );  
   }
#endif
}

#if 0
logic::weight_t logic::kbo::weight( const term& t ) 
{
   switch( t.sel()) 
   {
   case logic::sel_ident: 
   case logic:: sel_debruijn:
   case logic::sel_infset:
   case logic::sel_emptyset:
   case logic::sel_false:
   case logic::sel_true:
      return 1;
   
   case logic::prf_and2:
   case logic::prf_ext1:
   case logic::prf_taut:
   case logic::prf_and1:
   case logic::sel_unique:
   case logic::sel_pow:
   case logic::sel_union:
   case logic::prf_ext2:
   case logic::sel_not:
      {
         auto unary_t = t.view_unary();
         return 1 + weight( unary_t.sub() );
      }
   case logic::sel_and:
   case logic::sel_or:
   case logic::sel_implies:
   case logic::sel_equiv:
   case logic::sel_sep:
   case logic::sel_in:
   case logic::sel_subset:
   case logic::sel_equals:
   case logic::sel_insert:
   case logic::sel_repl:
   case logic::prf_abbr:
   case logic::prf_inst:
      {
         auto binary_t = t.view_binary();
         return 1 + weight(binary_t.sub1()) + weight(binary_t.sub2());
      }

   case logic::prf_disj:
      {
         auto ternary_t = t. view_ternary( );
         return 1 + weight( ternary_t. sub1( )) + weight( ternary_t. sub2( )) 
                  + weight( ternary_t. sub3( )); 
      }
   case logic::sel_appl: 
      {
         weight_t w = 0;
         auto appl_t = t.view_appl();
         for(size_t i=0; i<appl_t.size(); ++i)
            w += weight(appl_t.arg(i));
         w += weight(appl_t.func());
         return w;
      }
   case logic::sel_lambda:
      {
         auto lambda_t = t.view_lambda();
         return 1 + lambda_t.size() + weight(lambda_t.body());
      }
   case logic::sel_forall:
   case logic::sel_exists: 
      {
         auto quant_t = t.view_quant();
         return 1 + weight(quant_t.body());
      }
   case logic::prf_exp:
      {
         throw std::runtime_error( "incomplete, compare the positions" );
         auto exp_t = t.view_exp( );
         return 1 + weight( exp_t. body( ));
      }

   default:
      throw std::logic_error("no maching selector in weight()");  
   }
}
#endif

std::strong_ordering
logic::kbo::topleftright( const type& tp1, const type& tp2 ) 
{
   if( tp1. sel( ) < tp2. sel( ))
      return std::strong_ordering::less;
   if( tp1. sel( ) > tp2. sel( ))
      return std::strong_ordering::greater;
 
   switch( tp1. sel()) 
   {
   case type_form:
   case type_obj:
      return std::strong_ordering::equal;

   case type_struct:
      {
         auto s1 = tp1. view_struct( ). def( );
         auto s2 = tp2. view_struct( ). def( );
         if( s1 < s2 ) return std::strong_ordering::less;
         if( s1 > s2 ) return std::strong_ordering::greater;
         return std::strong_ordering::equal;
      } 
  
   case type_unchecked:
      { 
         identifier id1 = tp1. view_unchecked( ). id( );
         identifier id2 = tp2. view_unchecked( ). id( ); 
         return id1 <=> id2;
      }

   case logic::type_func:
      {
         auto func1 = tp1. view_func( );
         auto func2 = tp2. view_func( );

         std::strong_ordering ord =  
            topleftright( func1. result( ), func2. result( ) );

         if( ord != std::strong_ordering::equal )
            return ord;

         if( func1. size( ) < func2. size( )) 
            return std::strong_ordering::less;
         if( func1. size( ) > func2. size( )) 
            return std::strong_ordering::greater;

         for( size_t i = 0; i < func1. size(); ++i ) 
         {
            ord = topleftright( func1. arg(i), func2. arg(i) );
            if( ord != std::strong_ordering::equal )
               return ord;
         }

         return std::strong_ordering::equal;
      }

   default:
      std::cout << "the selector is " << tp1. sel( ) << "\n";
      throw std::logic_error("unknown selector in topleftright()");
   }
}

#if 0
std::strong_ordering
logic::kbo::topleftright( const term& t1, const term& t2 ) 
{
   if( t1. sel( ) < t2. sel( ))
      return std::strong_ordering::less;

   if( t1. sel( ) > t2. sel( ))
      return std::strong_ordering::greater;
 
   switch(t1.sel()) {
      case logic::prf_disj:
         {
            auto ternary_t1 = t1. view_ternary();
            auto ternary_t2 = t2. view_ternary();

            auto ord = topleftright( ternary_t1. sub1(), ternary_t2. sub1());
            if(ord != std::strong_ordering::equal) 
               return ord;
            
            ord = topleftright( ternary_t1. sub2(), ternary_t2. sub2());
            if(ord != std::strong_ordering::equal) 
               return ord;

            ord = topleftright( ternary_t1. sub3(), ternary_t2. sub3());
            return ord;
         }
      case logic::sel_and:
      case logic::sel_or:
      case logic::sel_implies:
      case logic::sel_equiv:
      case logic::sel_sep:
      case logic::sel_in:
      case logic::sel_subset:
      case logic::sel_equals:
      case logic::sel_insert:
      case logic::sel_repl:
      case logic::prf_inst:
         {
            auto binary_t1 = t1. view_binary();
            auto binary_t2 = t2. view_binary();

            auto ord = topleftright( binary_t1. sub1(), binary_t2. sub1());
            if( ord != std::strong_ordering::equal )
               return ord;
            
            ord = topleftright( binary_t1. sub2(), binary_t2. sub2());
            return ord;
         }
      case logic::prf_and2:
      case logic::prf_ext1:
      case logic::prf_taut:
      case logic::prf_and1:
      case logic::sel_unique:
      case logic::sel_pow:
      case logic::sel_union:
      case logic::prf_ext2:
      case logic::sel_not:
         {
            auto unary_t1 = t1.view_unary();
            auto unary_t2 = t2.view_unary();

            return topleftright(unary_t1. sub(), unary_t2. sub());
         }
      case logic::sel_infset:
      case logic::sel_emptyset:
      case logic::sel_false:
      case logic::sel_true:
         return std::strong_ordering::equal;
      case logic::sel_appl:
         {
            auto appl_t1 = t1.view_appl();
            auto appl_t2 = t2.view_appl();
            
            auto ord = topleftright(appl_t1. func(), appl_t2. func());
            if(ord != std::strong_ordering::equal)
               return ord;

            ord = appl_t1. size( ) <=> appl_t2. size( ); 
            if( !is_eq( ord )) 
               return ord;

            for(size_t i = 0; i < appl_t1. size(); ++i) {
               ord = topleftright( appl_t1. arg(i), appl_t2. arg(i));
               if( !is_eq( ord ))
                  return ord;
            }
            
            return std::strong_ordering::equal;
         }
      case logic::sel_lambda:
         {
            auto lambda_t1 = t1.view_lambda();
            auto lambda_t2 = t2.view_lambda();

            auto ord = topleftright(lambda_t1. body(), lambda_t2. body());
            if( !is_eq( ord ))
               return ord;

            if(lambda_t1. size() < lambda_t2. size())
               return std::strong_ordering::equal;
            if(lambda_t1. size() > lambda_t2. size())
               return std::strong_ordering::equal;

            for(size_t i = 0; i < lambda_t1. size(); ++i) {
               ord = topleftright(lambda_t1 .var(i). tp, lambda_t2 . var(i). tp);
               if( !is_eq( ord ))
                  return ord;
            }

            return std::strong_ordering::equal;
         }
      case logic::sel_exists:
      case logic::sel_forall:
         {
            auto quant_t1 = t1. view_quant();
            auto quant_t2 = t2. view_quant();

            auto ord = topleftright(quant_t1. var(). tp, quant_t2. var(). tp);
            if( !is_eq( ord ))
               return ord;

            ord = topleftright(quant_t1. body(), quant_t2. body());
            return ord;
         }
      case logic::sel_debruijn: 
         {
            auto ind1 = t1. view_debruijn(). index( );
            auto ind2 = t2. view_debruijn(). index( );

            return ind1 <=> ind2; 
         }
      case logic::sel_ident:
         {
            auto id1 = t1. view_id(). ident();
            auto id2 = t2. view_id(). ident();

            normident::equal_to eq; 
            if( eq( id1, id2 ))
               return std::strong_ordering::equal;

            if( id1. value( ) < id2. value( ))
               return std::strong_ordering::less;
            else
               return std::strong_ordering::greater; 
         }
      default:
         throw std::logic_error("no matching selector in topleftright()");
   }
}
#endif

void logic::kbo::print( std::strong_ordering ord, std::ostream& out )
{
   if( ord == std::strong_ordering::less )
   {
      out << "less"; 
      return;
   }

   if( ord == std::strong_ordering::greater )
   {
      out << "greater"; 
      return;
   }

   if( ord == std::strong_ordering::equal )
   {
      out << "equal"; 
      return;
   }

   if( ord == std::strong_ordering::equivalent )
   {
      out << "equivalent";
      return;
   }

   throw std::logic_error( "unknown order type" ); 
}

