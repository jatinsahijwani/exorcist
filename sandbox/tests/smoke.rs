#[tokio::test]
async fn sandbox_starts() -> anyhow::Result<()> {
    let worker = near_workspaces::sandbox().await?;
    let acc = worker.dev_create_account().await?;
    println!("sandbox ok, dev account {}", acc.id());
    Ok(())
}
