include "console.iol"

type Msg: any { ? }

interface ProcessApi {
    OneWay:
        msg( Msg )
}

service Ip {
    inputPort IpInput {
        location: "socket://localhost:8080"
        protocol: http { format = "json" }
        interfaces: ProcessApi
    }

    outputPort Client {
        location: "socket://localhost:8082"
        protocol: http { format = "json" }
        interfaces: ProcessApi
    }

    outputPort Server {
        location: "socket://localhost:8081"
        protocol: http { format = "json" }
        interfaces: ProcessApi
    }

    main {
        msg( request );
        println@Console( "username: " + request.username)();
        println@Console( "password: " + request.password)();
        if (request.username == "john" && request.password == "smith") {
            msg@Client("left");
            msg@Server("left")
        } else {
            msg@Client("right");
            msg@Server("right")
        }
    }
}
