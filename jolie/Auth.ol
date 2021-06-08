from console import Console

type Msg: any { ? }

interface ProcessApi {
    OneWay:
        msg( Msg )
}

service Ip {
    embed Console as console

    inputPort input {
        location: "socket://localhost:8080"
        protocol: http { format = "json" }
        interfaces: ProcessApi
    }

    outputPort server {
        location: "socket://localhost:8081"
        protocol: http { format = "json" }
        interfaces: ProcessApi
    }

    outputPort client {
        location: "socket://localhost:8082"
        protocol: http { format = "json" }
        interfaces: ProcessApi
    }

    main {
        msg( request );
        println@console( "username: " + request.username)();
        println@console( "password: " + request.password)();
        if (request.username == "john" && request.password == "smith") {
            msg@client("left");
            msg@server("left")
        } else {
            msg@client("right");
            msg@server("right")
        }
    }
}

service Server {
    inputPort input {
        location: "socket://localhost:8081"
        protocol: http { format = "json" }
        interfaces: ProcessApi
    }

    outputPort client {
        location: "socket://localhost:8082"
        protocol: http { format = "json" }
        interfaces: ProcessApi
    }

    main {
        msg( choice );
        if (choice == "left") {
            msg@client( "super-secret-token-42" )
        }
    }
}

service Client {
    embed Console as console

    inputPort input {
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
        println@console( "choice: " + choice )();
        if (choice == "left") {
            msg( token )
            println@console( "authenticated: " + token )()
        } else {
            println@console( "unauthenticated" )()
        }
    }
}
