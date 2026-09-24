/** Toys: FlockIt / Flockers sandbox card. */

export function FlockersPage() {
  return (
    <main className="page notes">
      <h1>Flockers</h1>
      <p className="lede">
        A playable UE flock sandbox and the Unreal plugin behind it.
      </p>

      <h2>What it is</h2>
      <p>
        FlockIt is a flocking plugin for Unreal Engine. Flockers is the public
        BellToy simulation sandbox where you can poke the same flock ideas in
        the browser. Built for playable crowd / agent motion, not for the hire
        graph.
      </p>

      <h2>Screenshots</h2>
      <figure>
        <img
          className="note-fig"
          src="/toys/flockers/sandbox-hero.jpg"
          alt="Flockers sandbox hero"
        />
        <figcaption>Sandbox — flockers.halfasecond.com</figcaption>
      </figure>
      <figure>
        <img
          className="note-fig"
          src="/toys/flockers/product-promo1.jpg"
          alt="FlockIt flock in Unreal"
        />
        <figcaption>FlockIt in Unreal</figcaption>
      </figure>
      <figure>
        <img
          className="note-fig"
          src="/toys/flockers/product-promo2.jpg"
          alt="FlockIt agents in a scene"
        />
        <figcaption>Agents in a scene</figcaption>
      </figure>
      <figure>
        <img
          className="note-fig"
          src="/toys/flockers/product-promo3.jpg"
          alt="FlockIt flock from another angle"
        />
        <figcaption>Another angle</figcaption>
      </figure>

      <h2>Links</h2>
      <ul>
        <li>
          <strong>Sandbox</strong> —{" "}
          <a
            href="https://flockers.halfasecond.com/"
            target="_blank"
            rel="noreferrer"
          >
            flockers.halfasecond.com
          </a>
        </li>
        <li>
          <strong>Product</strong> —{" "}
          <a href="https://flockit.xyz/" target="_blank" rel="noreferrer">
            flockit.xyz
          </a>
        </li>
        <li>
          <strong>Unreal plugin</strong> —{" "}
          <a
            href="https://www.fab.com/listings/7c5fcbfb-ff80-4b4a-9b77-688af87f2f12"
            target="_blank"
            rel="noreferrer"
          >
            Fab listing
          </a>
        </li>
      </ul>

      <h2>How to poke it</h2>
      <p>
        Open the sandbox link, run the flock, and nudge the controls. For the
        plugin path, start from flockit.xyz or the Fab listing and drop it into
        an Unreal project.
      </p>
    </main>
  );
}
