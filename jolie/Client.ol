include "console.iol"

type Msg: any { ? }

interface ProcessApi {
    OneWay:
        msg( Msg )
}

service Client {
    inputPort ClientInput {
        location: "socket://localhost:8082"
        protocol: http { format = "json" }
        interfaces: ProcessApi
    }

    outputPort Ip {
        location: "socket://localhost:8080"
        protocol: http { format = "json" }
        interfaces: ProcessApi
    }

    main {
        // credentials = { .username = "john", .password = "smith" };
        // msg@Ip( credentials );
        msg@Ip( { .username = "john", .password = "smith" } );
        // TODO: Race condition. We could first receive the choice from Ip, or
        // the token from Server. We need to have a way of waiting for a message
        // from a specific recipient. Either have multiple operations, or
        // multiplex everything over a single operation.
        msg( choice );
        println@Console( "choice: " + choice )();
        if (choice == "left") {
            msg( token )
            println@Console( "authenticated: " + token )()
        } else {
            println@Console( "unauthenticated" )()
        }
    }
}
