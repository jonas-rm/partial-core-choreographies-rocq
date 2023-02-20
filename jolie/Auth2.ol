from console import Console

type Msg: any { ? }
type Label: string {}

interface IpApi {
    OneWay:
        comClient( Msg )
}

interface ServerApi {
    OneWay:
        selIp( Label )
}

interface ClientApi {
    OneWay:
        comServer( Msg ),
        selIp( Label )
}

service Ip {
    embed Console as Console

    inputPort Input {
        location: "socket://localhost:8080"
        protocol: http { format = "json" }
        interfaces: IpApi
    }

    outputPort Server {
        location: "socket://localhost:8081"
        protocol: http { format = "json" }
        interfaces: ServerApi
    }

    outputPort Client {
        location: "socket://localhost:8082"
        protocol: http { format = "json" }
        interfaces: ClientApi
    }

    main {
        comClient( request );
        println@Console( "username: " + request.username)();
        println@Console( "password: " + request.password)();
        if (request.username == "john" && request.password == "smith") {
            selIp@Client( "left" );
            selIp@Server( "left" )
        } else {
            selIp@Client( "right" );
            selIp@Server( "right" )
        }
    }
}

service Server {
    inputPort Input {
        location: "socket://localhost:8081"
        protocol: http { format = "json" }
        interfaces: ServerApi
    }

    outputPort Client {
        location: "socket://localhost:8082"
        protocol: http { format = "json" }
        interfaces: ClientApi
    }

    main {
        selIp( label );
        if (label == "left") {
            comServer@Client( "super-secret-token-42" )
        }
    }
}

service Client {
    embed Console as Console

    inputPort Input {
        location: "socket://localhost:8082"
        protocol: http { format = "json" }
        interfaces: ClientApi
    }

    outputPort Ip {
        location: "socket://localhost:8080"
        protocol: http { format = "json" }
        interfaces: IpApi
    }

    main {
        comClient@Ip( { .username = "john", .password = "smith" } );
        selIp( label );
        println@Console( "label: " + label )();
        if (label == "left") {
            comServer( token )
            println@Console( "authenticated: " + token )()
        } else {
            println@Console( "unauthenticated" )()
        }
    }
}
