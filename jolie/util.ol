from console import Console

interface UtilApi {
RequestResponse:
    check( undefined )( bool ),
    makeToken( void )( string ),

OneWay:
    println( string )
}

service Util {
    execution: sequential

    embed Console as Console

    inputPort Util {
        location: "local"
        interfaces: UtilApi
    }

    main {
        [ check( creds )( r ) {
            println@Console( "check!" )()
            r = true
        } ] {
            println@Console( "check done!" )()
        }

        [ makeToken()( r ) {
            println@Console( "makeToken!" )()
            r = new
        } ] {
            println@Console( "makeToken done!" )()
        }

        [ println( s ) ] {
            println@Console( s )()
            println@Console( "println done!" )()
        }
    }
}
