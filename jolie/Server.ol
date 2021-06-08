type Msg: any { ? }

interface ProcessApi {
    OneWay:
        msg( Msg )
}

service Server {
    inputPort ServerInput {
        location: "socket://localhost:8081"
        protocol: http { format = "json" }
        interfaces: ProcessApi
    }

    outputPort Client {
        location: "socket://localhost:8082"
        protocol: http { format = "json" }
        interfaces: ProcessApi
    }

    main {
        msg( choice );
        if (choice == "left") {
            msg@Client( "super-secret-token-42" )
        }
    }
}
